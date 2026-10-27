module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Inner

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family

section Arith

variable {G : Type*} [Group G]

theorem index_inf_le_of_le {F F' C : Subgroup G} (hF : F ≤ C) (hF' : F' ≤ C)
    (hFi : F.index = 64) (hFi' : F'.index = 64) (hC : 32 ≤ C.index) :
    (F ⊓ F').index ≤ 128 := by
  have h1 := Subgroup.relIndex_mul_index hF
  have h2 := Subgroup.relIndex_mul_index hF'
  have h3 := Subgroup.relIndex_mul_index (inf_le_left.trans hF : F ⊓ F' ≤ C)
  have h4 : (F ⊓ F').relIndex C ≤ F.relIndex C * F'.relIndex C := Subgroup.relIndex_inf_le
  rw [hFi] at h1
  rw [hFi'] at h2
  have ha : F.relIndex C ≤ 2 := by
    by_contra h
    push Not at h
    have h5 : 3 * 32 ≤ F.relIndex C * C.index := Nat.mul_le_mul h hC
    omega
  calc (F ⊓ F').index = (F ⊓ F').relIndex C * C.index := h3.symm
    _ ≤ (F.relIndex C * F'.relIndex C) * C.index := Nat.mul_le_mul_right _ h4
    _ = F.relIndex C * (F'.relIndex C * C.index) := by ring
    _ = F.relIndex C * 64 := by rw [h2]
    _ ≤ 2 * 64 := Nat.mul_le_mul_right _ ha

theorem index_inf_inf_le {F X Y : Subgroup G} (hX : X ≤ F) (hY : Y ≤ F) (hFi : F.index = 64)
    (hXi : X.index ≤ 128) (hYi : Y.index ≤ 128) : (X ⊓ Y).index ≤ 256 := by
  have h1 := Subgroup.relIndex_mul_index hX
  have h2 := Subgroup.relIndex_mul_index hY
  have h3 := Subgroup.relIndex_mul_index (inf_le_left.trans hX : X ⊓ Y ≤ F)
  have h4 : (X ⊓ Y).relIndex F ≤ X.relIndex F * Y.relIndex F := Subgroup.relIndex_inf_le
  rw [hFi] at h1 h2 h3
  have ha : X.relIndex F ≤ 2 := by omega
  have hb : Y.relIndex F ≤ 2 := by omega
  have h5 : X.relIndex F * Y.relIndex F ≤ 2 * 2 := Nat.mul_le_mul ha hb
  omega

end Arith

section Red

variable {W : Type} [CommGroup W] [Finite W]

theorem eq_of_redHom_eq_of_sq (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) {S : Type} [Group S] (e : CQ L ≃* S) {u v : ↥L} (hu : u * u = 1)
    (hv : v * v = 1) (h : redHom L e u = redHom L e v) : u = v := by
  have hz : u * v⁻¹ ∈ Subgroup.center ↥L := by
    rw [← redHom_eq_one_iff L e, map_mul, map_inv, h, mul_inv_cancel]
  have hcomm : ∀ l ∈ L, l * ((u * v⁻¹ : ↥L) : MulAut W) = ((u * v⁻¹ : ↥L) : MulAut W) * l := by
    intro l hl
    have := Subgroup.mem_center_iff.1 hz ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hodd := odd_orderOf_of_commutes hW hirr hcomm
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have h1 : v * u * v = u := by
    have := Subgroup.mem_center_iff.1 hz v
    rw [hv'] at this
    calc v * u * v = v * (u * v) := mul_assoc _ _ _
      _ = u * v * v := this
      _ = u * (v * v) := mul_assoc _ _ _
      _ = u := by rw [hv, mul_one]
  have hz2 : (u * v⁻¹) * (u * v⁻¹) = 1 := by
    rw [hv']
    calc (u * v) * (u * v) = u * (v * u * v) := by simp only [mul_assoc]
      _ = u * u := by rw [h1]
      _ = 1 := hu
  have hz2' : ((u * v⁻¹ : ↥L) : MulAut W) ^ 2 = 1 := by
    rw [sq, ← Subgroup.coe_mul, hz2]
    rfl
  have hdvd : orderOf ((u * v⁻¹ : ↥L) : MulAut W) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2'
  have h1' : orderOf ((u * v⁻¹ : ↥L) : MulAut W) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have h0 : (u * v⁻¹ : ↥L) = 1 := Subtype.ext (orderOf_eq_one_iff.1 h1')
  exact mul_inv_eq_one.1 h0

theorem exists_mem_conjSub (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) (hEL : E ≤ L) (hEel : IsElemAbelian2 E) {S : Type} [Group S]
    (e : CQ L ≃* S) (ĝ : ↥L) {b : S} (hb : b ∈ imgSub L E hEL e)
    (hb' : (redHom L e ĝ)⁻¹ * b * redHom L e ĝ ∈ imgSub L E hEL e) :
    ∃ x : ↥E, redHom L e (Subgroup.inclusion hEL x) = b ∧
      (x : MulAut W) ∈ conjSub (ĝ : MulAut W) E := by
  obtain ⟨x, hx⟩ := mem_imgSub.1 hb
  obtain ⟨y, hy⟩ := mem_imgSub.1 hb'
  refine ⟨x, hx, ?_⟩
  have hsq : ∀ z : ↥E, Subgroup.inclusion hEL z * Subgroup.inclusion hEL z = 1 := by
    intro z
    have : z * z = 1 := Subtype.ext (by simpa [sq] using hEel.2 z z.2)
    rw [← map_mul, this, map_one]
  have hu : (ĝ⁻¹ * Subgroup.inclusion hEL x * ĝ) * (ĝ⁻¹ * Subgroup.inclusion hEL x * ĝ) = 1 := by
    calc (ĝ⁻¹ * Subgroup.inclusion hEL x * ĝ) * (ĝ⁻¹ * Subgroup.inclusion hEL x * ĝ)
        = ĝ⁻¹ * (Subgroup.inclusion hEL x * Subgroup.inclusion hEL x) * ĝ := by group
      _ = 1 := by rw [hsq x]; group
  have hred : redHom L e (ĝ⁻¹ * Subgroup.inclusion hEL x * ĝ) =
      redHom L e (Subgroup.inclusion hEL y) := by
    rw [hy, map_mul, map_mul, map_inv, hx]
  have heq := eq_of_redHom_eq_of_sq hW hirr e hu (hsq y) hred
  rw [mem_conjSub]
  refine ⟨(y : MulAut W), y.2, ?_⟩
  have h2 : ((ĝ⁻¹ * Subgroup.inclusion hEL x * ĝ : ↥L) : MulAut W) = (y : MulAut W) := by
    rw [heq]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] at h2
  rw [← h2]
  group

end Red

section Chain

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def Gen11 (S : Type) [Group S] : Prop :=
  ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → 2 < Nat.card B →
    ∃ cs : List S, cs.length = 2 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S)), orderOf x = 11

theorem two_pow_five_le_index (hW : ∀ w : W, w * w = 1) {L K : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) (hKL : K ≤ L) (hKel : IsElemAbelian2 K) {S : Type} [Group S]
    (e : CQ L ≃* S) (hgen11 : Gen11 S) (h3 : 2 < Nat.card K) : 2 ^ 5 ≤ (fixV K).index := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hBcard := card_imgSub hW hirr hKL hKel e
  obtain ⟨cs, hcs, hx⟩ := hgen11 (imgSub L K hKL e) (imgSub_comm (hEL := hKL) (e := e) hKel)
    (imgSub_sq (hEL := hKL) (e := e) hKel) (by rw [hBcard]; exact h3)
  have h := two_pow_le_of_inner_gen hW hKL e (k := 2) (p := 11) (by norm_num) ⟨cs, hcs, hx⟩
  rw [orderOf_two_zmod_11] at h
  exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW K) h (ρ := 5) (by norm_num)

omit [Finite W] in
theorem fixV_conjSup_eq_bot {L : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    (hirr : IsIrrOn L) (hL : L ≠ ⊥) {S : Type} [Group S] (e : CQ L ≃* S)
    {B : Subgroup (MulAut W)} (cs' : List ↥L)
    (hgen : Subgroup.closure {y : S | ∃ c ∈ cs'.map (redHom L e), ∃ b : ↥L,
      (b : MulAut W) ∈ B ∧ y = c * e (QuotientGroup.mk b) * c⁻¹} = ⊤) :
    fixV (conjSup B (liftW cs')) = ⊥ := by
  have hker : (redHom L e).ker = Subgroup.center ↥L := by
    ext x
    exact redHom_eq_one_iff L e x
  set J : Subgroup ↥L := Subgroup.closure (conjGen B cs') with hJ
  have hmap : J.map (redHom L e) = ⊤ := by
    rw [hJ, map_closure_conjGen (redHom L e) B cs']
    exact hgen
  have hsup : J ⊔ Subgroup.center ↥L = ⊤ := by
    rw [← hker, ← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
  have hJtop : J = ⊤ := eq_top_of_sup_center_eq_top hperf hsup
  have hLle : L ≤ conjSup B (liftW cs') := by
    intro g hg
    apply map_closure_conjGen_le B cs'
    rw [← hJ, hJtop]
    exact Subgroup.mem_map.2 ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩
  exact eq_bot_iff.2 (fun v hv => by
    have : v ∈ fixV L := fixV_anti hLle hv
    rw [fixV_eq_bot_of_irr hirr hL] at this
    exact this)

@[expose] def AdjCert {S : Type} [Group S] (El : List S) (g : S) : Prop :=
  ∃ b₁ ∈ El, ∃ b₂ ∈ El, b₁ ≠ 1 ∧ b₂ ≠ 1 ∧ b₁ ≠ b₂ ∧ g⁻¹ * b₁ * g ∈ El ∧ g⁻¹ * b₂ * g ∈ El

theorem tight_chain_false (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L) (hL : L ≠ ⊥) {S : Type} [Group S]
    (e : CQ L ≃* S) (hgen11 : Gen11 S) (hEL : E ≤ L) (hEel : IsElemAbelian2 E)
    (hidx : (fixV E).index = 64) (hWbig : 256 < Nat.card W) (El : List S)
    (hT : ∀ x, x ∈ imgSub L E hEL e ↔ x ∈ El) (g₂ g₃ : S) (hadj₂ : AdjCert El g₂)
    (hadj₃ : AdjCert El g₃)
    (hgen : Subgroup.closure (conjSet [1, g₂, g₃] {x : S | x ∈ El}) = ⊤) : False := by
  have adj : ∀ (ĝ : ↥L) (g : S), redHom L e ĝ = g → AdjCert El g →
      (fixV E ⊓ fixV (conjSub (ĝ : MulAut W) E)).index ≤ 128 := by
    rintro ĝ g hĝ ⟨b₁, hb₁, b₂, hb₂, h1, h2, h12, hc₁, hc₂⟩
    have hcc₁ : (redHom L e ĝ)⁻¹ * b₁ * redHom L e ĝ ∈ imgSub L E hEL e := by
      rw [hĝ]
      exact (hT _).2 hc₁
    have hcc₂ : (redHom L e ĝ)⁻¹ * b₂ * redHom L e ĝ ∈ imgSub L E hEL e := by
      rw [hĝ]
      exact (hT _).2 hc₂
    obtain ⟨x₁, hx₁, hx₁c⟩ := exists_mem_conjSub hW hirr hEL hEel e ĝ ((hT b₁).2 hb₁) hcc₁
    obtain ⟨x₂, hx₂, hx₂c⟩ := exists_mem_conjSub hW hirr hEL hEel e ĝ ((hT b₂).2 hb₂) hcc₂
    set K : Subgroup (MulAut W) := E ⊓ conjSub (ĝ : MulAut W) E with hK
    have hKL : K ≤ L := inf_le_left.trans hEL
    have hKel : IsElemAbelian2 K :=
      ⟨fun a ha b hb => hEel.1 a ha.1 b hb.1, fun a ha => hEel.2 a ha.1⟩
    have hx₁K : (x₁ : MulAut W) ∈ K := ⟨x₁.2, hx₁c⟩
    have hx₂K : (x₂ : MulAut W) ∈ K := ⟨x₂.2, hx₂c⟩
    have hx₁ne : (x₁ : MulAut W) ≠ 1 := by
      intro h
      apply h1
      have hx1 : x₁ = 1 := Subtype.ext h
      rw [← hx₁, hx1]
      simp
    have hx₂ne : (x₂ : MulAut W) ≠ 1 := by
      intro h
      apply h2
      have hx1 : x₂ = 1 := Subtype.ext h
      rw [← hx₂, hx1]
      simp
    have hx₁₂ : (x₁ : MulAut W) ≠ (x₂ : MulAut W) := by
      intro h
      apply h12
      have hx1 : x₁ = x₂ := Subtype.ext h
      rw [← hx₁, ← hx₂, hx1]
    have hK3 : 2 < Nat.card K := by
      have hsub : ({1, (x₁ : MulAut W), (x₂ : MulAut W)} : Set (MulAut W)) ⊆
          (K : Set (MulAut W)) := by
        intro z hz
        rcases hz with rfl | rfl | rfl
        · exact K.one_mem
        · exact hx₁K
        · exact hx₂K
      have h3 : ({1, (x₁ : MulAut W), (x₂ : MulAut W)} : Set (MulAut W)).ncard = 3 := by
        rw [Set.ncard_eq_three]
        exact ⟨1, x₁, x₂, hx₁ne.symm, hx₂ne.symm, hx₁₂, rfl⟩
      have h4 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [h3, ← Nat.card_coe_set_eq] at h4
      exact h4
    have h5 := two_pow_five_le_index hW hirr hKL hKel e hgen11 hK3
    have hFK : fixV E ≤ fixV K := fixV_anti inf_le_left
    have hF'K : fixV (conjSub (ĝ : MulAut W) E) ≤ fixV K := fixV_anti inf_le_right
    exact index_inf_le_of_le hFK hF'K hidx ((index_fixV_conjSub _ _).trans hidx)
      (by simpa using h5)
  obtain ⟨ĝ₂, h2⟩ := redHom_surjective L e g₂
  obtain ⟨ĝ₃, h3⟩ := redHom_surjective L e g₃
  have hX := adj ĝ₂ g₂ h2 hadj₂
  have hY := adj ĝ₃ g₃ h3 hadj₃
  have hgen' : Subgroup.closure {y : S | ∃ c ∈ ([1, ĝ₂, ĝ₃] : List ↥L).map (redHom L e),
      ∃ b : ↥L, (b : MulAut W) ∈ E ∧ y = c * e (QuotientGroup.mk b) * c⁻¹} = ⊤ := by
    rw [← hgen]
    congr 1
    ext y
    simp only [List.map_cons, List.map_nil, map_one, h2, h3, Set.mem_ofPred_eq, conjSet]
    constructor
    · rintro ⟨c, hc, b, hbE, rfl⟩
      exact ⟨c, hc, e (QuotientGroup.mk b), (hT _).1 (mem_imgSub.2 ⟨⟨b, hbE⟩, rfl⟩), rfl⟩
    · rintro ⟨c, hc, t, ht, rfl⟩
      obtain ⟨a, ha⟩ := mem_imgSub.1 ((hT t).2 ht)
      exact ⟨c, hc, Subgroup.inclusion hEL a, a.2, by rw [← ha]; rfl⟩
  have hbot := fixV_conjSup_eq_bot hperf hirr hL e [1, ĝ₂, ĝ₃] hgen'
  have hc1 : conjSub (1 : MulAut W) E = E := by
    ext x
    simp [mem_conjSub]
  have hbot' : (fixV E ⊓ fixV (conjSub (ĝ₂ : MulAut W) E)) ⊓
      (fixV E ⊓ fixV (conjSub (ĝ₃ : MulAut W) E)) = ⊥ := by
    rw [← hbot]
    ext v
    simp only [conjSup, liftW, List.map_cons, List.map_nil, Subgroup.coe_one, fixV_sup, fixV_bot,
      hc1, Subgroup.mem_inf, Subgroup.mem_top, and_true]
    tauto
  have h256 := index_inf_inf_le (F := fixV E) inf_le_left inf_le_left hidx hX hY
  rw [hbot', Subgroup.index_bot] at h256
  omega

end Chain

end CFSG.QuasithinUnique.Setup.X1
