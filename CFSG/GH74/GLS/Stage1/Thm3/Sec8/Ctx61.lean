module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx60
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafBal
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic22
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic23

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem balance85 (hII : II4_4_4_center) (h327 : IG_3_27) (hF : FStar_C)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {d c : G} (hdS : d ∈ S) (hd2 : orderOf d = 2)
    (hint : Interchanges d K₁ K₂) (hc : c * z * c⁻¹ = d) :
    ∀ k ∈ Pof S K₁, k * (d * k * d⁻¹) ∈ conjugate (K₁ ⊔ K₂) c⁻¹ := by
  intro k hk
  have hM := hs.m4 hII
  have hstd := hs.fused.std
  have hdd : d * d = 1 := mul_self_eq_one_of_orderOf_eq_two hd2
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hK₁int : IsIntrinsic z K₁ := intrinsic_of_comp hM hstd (Or.inl rfl)
  have hdn : d ∉ normalizer (K₁ : Set G) := by
    intro hn
    have h1 : conjugate K₁ d = K₁ := by
      rw [← cj_eq_conjugate]; exact M.cj_eq_iff_normalizer.2 hn
    exact hstd.ne (h1.symm.trans hint.1)
  have hdC : d ∈ centralizer ({z} : Set G) := hs.S_le_C hII hdS
  have hcomm : Commute z d := (Subgroup.mem_centralizer_singleton_iff.1 hdC).symm
  have hzC : z ∈ centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hdC).symm
  obtain ⟨hI, -, -, hT⟩ := h327 G hstd.simple z d hstd.orderOf_z hd2 hcomm K₁ hK₁int hdn
  have hlayer : IDiag d K₁ ≤ pLayerOf 2 (centralizer ({d} : Set G)) :=
    le_pLayerOf_of_isPCompIn_inf hstd.orderOf_z hzC hI
  have hCd : centralizer ({d} : Set G) = cmap c (centralizer ({z} : Set G)) := by
    rw [← hc]
    exact (map_centralizer_singleton_conj z c).symm
  have hPL : pLayerOf 2 (centralizer ({d} : Set G)) ≤ cmap c (K₁ ⊔ K₂) := by
    rw [hCd, pLayerOf_cmap]
    exact Subgroup.map_mono (Sec7.Leaf.pLayerOf_Cz_le hII hF hstd hs.fused.hQ)
  have hSyl : CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In (Pz S z) (K₁ ⊔ conjugate K₁ d) := by
    rw [hint.1, Pz_eq hstd]
    exact hM.P_syl
  have hdN : d ∈ normalizer (Pz S z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hs.S_normalizes_Pz hII hdS x hx
    · intro hx
      have := hs.S_normalizes_Pz hII (inv_mem hdS) _ hx
      have e : d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x := by group
      rwa [e] at this
  obtain ⟨S₀, hS₀, hS₀eq⟩ := hT (Pz S z) hSyl hdN
  have hkP : k ∈ Pz S z ⊓ K₁ := by
    refine Subgroup.mem_inf.2 ⟨?_, hk.2⟩
    rw [Pz_eq hstd]
    exact Subgroup.mem_inf.2 ⟨hk.1, Subgroup.mem_sup_left hk.2⟩
  have hkS₀ : k * (d⁻¹ * k * d) ∈ (S₀ : Set G) := by
    rw [hS₀eq]
    exact ⟨k, hkP, rfl⟩
  have hkI : k * (d⁻¹ * k * d) ∈ IDiag d K₁ := hS₀.1 hkS₀
  have h1 := hPL (hlayer hkI)
  rw [mem_cmap] at h1
  rw [mem_conjugate_iff]
  rw [hdinv] at h1
  have e : d⁻¹ = d := hdinv
  rw [e]
  simpa [hdinv] using h1

theorem exists_diag' (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {δ : G} (hδS : δ ∈ S) (hδS1 : δ ∉ S1 S K₁) (hδ2 : δ * δ = 1) (hδu : δ * u * δ⁻¹ = u) :
    ∃ k₀ ∈ Pof S K₁, k₀ * (δ * k₀ * δ⁻¹) ∈ U ∧ k₀ * (δ * k₀ * δ⁻¹) ≠ 1 ∧ k₀ * (δ * k₀ * δ⁻¹) ≠ z := by
  obtain ⟨hδK₁, hδK₂⟩ := hs.swap_of_not_mem hII hδS hδS1
  obtain ⟨v₁, hv₁, v₂, hv₂, huv, -, -⟩ := hs.u_decomp hII hq
  have hv₁P : v₁ ∈ Pof S K₁ := hv₁.2
  have hv₂P : v₂ ∈ Pof S K₂ := hv₂.2
  have hk₀ : δ * v₂ * δ⁻¹ ∈ Pof S K₁ := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hδS hv₂P.1) (inv_mem hδS), ?_⟩
    have : v₂ ∈ conjugate K₁ δ := by rw [hδK₁]; exact hv₂P.2
    exact mem_conjugate_iff.1 this
  have hk₁ : δ * v₁ * δ⁻¹ ∈ Pof S K₂ := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hδS hv₁P.1) (inv_mem hδS), ?_⟩
    have : v₁ ∈ conjugate K₂ δ := by rw [hδK₂]; exact hv₁P.2
    exact mem_conjugate_iff.1 this
  have hcomm := hs.P_comm hII
  have hzz := hs.z_sq
  have hz1 := hs.z_ne
  have h1 : (δ * v₁ * δ⁻¹) * (δ * v₂ * δ⁻¹) = v₁ * v₂ := by
    have : δ * (v₁ * v₂) * δ⁻¹ = v₁ * v₂ := by rw [← huv]; exact hδu
    calc (δ * v₁ * δ⁻¹) * (δ * v₂ * δ⁻¹) = δ * (v₁ * v₂) * δ⁻¹ := by group
      _ = v₁ * v₂ := this
  have h2 : (δ * v₂ * δ⁻¹) * (δ * v₁ * δ⁻¹) = v₁ * v₂ := (hcomm _ hk₀ _ hk₁).trans h1
  have h3 : v₁⁻¹ * (δ * v₂ * δ⁻¹) = v₂ * (δ * v₁ * δ⁻¹)⁻¹ := by
    calc v₁⁻¹ * (δ * v₂ * δ⁻¹) = v₁⁻¹ * ((δ * v₂ * δ⁻¹) * (δ * v₁ * δ⁻¹)) * (δ * v₁ * δ⁻¹)⁻¹ := by group
      _ = v₁⁻¹ * (v₁ * v₂) * (δ * v₁ * δ⁻¹)⁻¹ := by rw [h2]
      _ = v₂ * (δ * v₁ * δ⁻¹)⁻¹ := by group
  have hmem : v₁⁻¹ * (δ * v₂ * δ⁻¹) ∈ Pof S K₁ ⊓ Pof S K₂ := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hv₁P) hk₀, ?_⟩
    rw [h3]
    exact mul_mem hv₂P (inv_mem hk₁)
  rw [hs.P_inf hII] at hmem
  have hδk : δ * (δ * v₂ * δ⁻¹) * δ⁻¹ = v₂ := by
    calc δ * (δ * v₂ * δ⁻¹) * δ⁻¹ = (δ * δ) * v₂ * (δ * δ)⁻¹ := by group
      _ = v₂ := by rw [hδ2]; group
  have hu1 : u ≠ 1 := fun e => hs.u_ne (by rw [e]; exact one_mem _)
  have huz : u ≠ z := fun e => hs.u_ne (by rw [e]; exact Subgroup.mem_zpowers z)
  refine ⟨δ * v₂ * δ⁻¹, hk₀, ?_⟩
  rw [hδk]
  rcases (Basic.mem_zpowers_of_sq' hzz).1 hmem with h0 | h0
  · have hk : δ * v₂ * δ⁻¹ = v₁ := by
      calc δ * v₂ * δ⁻¹ = v₁ * (v₁⁻¹ * (δ * v₂ * δ⁻¹)) := by group
        _ = v₁ := by rw [h0, mul_one]
    rw [hk, ← huv]
    exact ⟨hs.u_mem, hu1, huz⟩
  · have hk : δ * v₂ * δ⁻¹ = v₁ * z := by
      calc δ * v₂ * δ⁻¹ = v₁ * (v₁⁻¹ * (δ * v₂ * δ⁻¹)) := by group
        _ = v₁ * z := by rw [h0]
    have hzv : z * v₂ = v₂ * z := hs.z_comm hII hv₂P.1
    have hval : v₁ * z * v₂ = u * z := by
      calc v₁ * z * v₂ = v₁ * (z * v₂) := by group
        _ = v₁ * (v₂ * z) := by rw [hzv]
        _ = (v₁ * v₂) * z := by group
        _ = u * z := by rw [← huv]
    rw [hk, hval]
    refine ⟨mul_mem hs.u_mem hs.z_mem, ?_, ?_⟩
    · intro e
      apply huz
      have : u = z⁻¹ := eq_inv_of_mul_eq_one_left e
      rw [this]
      exact inv_eq_of_mul_eq_one_right hzz
    · intro e
      apply hu1
      have : u * z = 1 * z := by rw [e, one_mul]
      exact mul_right_cancel this

theorem lemma85_false' (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) (h41 : Prop4_1)
    (hbal : ∀ {d c : G}, d ∈ S → orderOf d = 2 → Interchanges d K₁ K₂ → c * z * c⁻¹ = d →
      ∀ k ∈ Pof S K₁, k * (d * k * d⁻¹) ∈ conjugate (K₁ ⊔ K₂) c⁻¹)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : 2 ^ 7 ≤ Nat.card ↥S)
    (hcon : ∀ w ∈ Wsub S U, w * h * w⁻¹ * h⁻¹ ∈ Aof S K₁ W₂ h) : False := by
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  have hA16 : Nat.card ↥(Aof S K₁ W₂ h) = 16 := by
    have := hs.card_A hII hq hrec hk
    norm_num at this
    omega
  have hAc := hs.A_comm hII hq hrec
  have hZ := hs.A_equiv_Z4Z4 hII hq hrec hk
  have hAW : Aof S K₁ W₂ h ≤ Wsub S U := hs.A_le_W hII hq hrec (k := 1 + 1) (by norm_num) hk
  have hNA := hs.N_le_normalizer_A hII hq hrec hk
  have hWN : Wsub S U ≤ normalizer ((Aof S K₁ W₂ h : Subgroup G) : Set G) := fun w hw =>
    hNA ((le_sup_left : S ≤ S ⊔ zpowers h) hw.1)
  have hh := hs.h_mem_normalizer_A hII hq hrec hk
  have hhord := hs.orderOf_conjAut_h hII hq hrec hk
  have hW2 : ∀ w ∈ Wsub S U, ∃ k : ℕ, w ^ (2 ^ k) = 1 := by
    intro w hw
    obtain ⟨k, hk⟩ := (hs.S_pgroup hII) ⟨w, hw.1⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcentA : ∀ w ∈ Wsub S U, (∀ a ∈ Aof S K₁ W₂ h, w * a = a * w) → w ∈ Aof S K₁ W₂ h := by
    intro w hw hc
    have : w ∈ S ⊓ centralizer ((Aof S K₁ W₂ h : Subgroup G) : Set G) :=
      ⟨hw.1, Subgroup.mem_centralizer_iff.2 (fun a ha => (hc a ha).symm)⟩
    rwa [hs.cent_eq hII hq hrec] at this
  have hUA : U ≤ Aof S K₁ W₂ h := hs.U_le_A hII hq hrec (k := 1 + 1) (by norm_num) hk
  have hUiff : ∀ x, x ∈ U ↔ x ∈ Aof S K₁ W₂ h ∧ x * x = 1 := fun x =>
    ⟨fun hx => ⟨hUA hx, hs.four_sq x hx⟩, fun hx => hs.A_inv_mem_U hII hq hrec hx.1 hx.2⟩
  have hUh : ∀ x ∈ U, h * x * h⁻¹ ∈ U := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hs.h_norm x).1 hx
  have hUh' : ∀ x ∈ U, h⁻¹ * x * h ∈ U := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hs.h_norm) x).1 hx
    simpa using this
  have hcube : ∀ x ∈ U, h ^ 3 * x = x * h ^ 3 := fun x hx => hs.h_cube x (hs.U_le_W' hII x hx)
  have hfree := (Basic.U_orbit hs.U_four.2 hs.z_mem hs.z_ne hUh hUh' hcube hs.h_move).1
  have hC1 : ∀ a ∈ Aof S K₁ W₂ h, h * a * h⁻¹ = a → a = 1 :=
    Basic.centralizer_trivial hZ hUiff hfree
  have hSW := hs.card_S_eq_two_W hII hq hk
  have hWcard : 4 * Nat.card ↥(Aof S K₁ W₂ h) ≤ Nat.card ↥(Wsub S U) := by
    rw [hA16]
    norm_num at hS7
    omega
  obtain ⟨hWle, δ, hδW, hδ2, hδh, P1, P2⟩ :=
    Basic.core85 hAc hZ hAW hWN hW2 hh hhord hcentA hC1 hcon hWcard
  have hS128 : Nat.card ↥S = 2 ^ 7 := by
    rw [hA16] at hWle
    norm_num
    omega
  have hδS : δ ∈ S := hδW.1
  have hδS1 : δ ∉ S1 S K₁ := by
    intro hδ1
    refine Basic.not_normalize_cyclic (A := Aof S K₁ W₂ h) (V := Vof S K₁ W₂)
      (le_sup_left) (by rw [hk]; norm_num) hs.V₁_cyclic (fun a ha h1 => (P1 a ha).1 h1) P2 ?_
    exact fun x hx => hs.V₁_normal hII δ hδ1 x hx
  have hAδ : ∀ a ∈ Aof S K₁ W₂ h, δ * a * δ⁻¹ ∈ Aof S K₁ W₂ h := fun a ha =>
    hs.A_normS hII hq hrec hδS ha
  obtain ⟨a₀, ha₀, hya⟩ := Basic.exists_sq_coset hAc hAδ hδ2 hUiff (Basic.exp4_of_Z4Z4 hZ) hA16
    hs.U_four.2 (fun a ha h1 => (P1 a ha).2 h1) P2 z hs.z_mem
  have hyS : a₀ * δ ∈ S := mul_mem (hs.A_le_S hII hq hrec ha₀) hδS
  have hyS1 : a₀ * δ ∉ S1 S K₁ := by
    intro hy
    apply hδS1
    have : δ = a₀⁻¹ * (a₀ * δ) := by group
    rw [this]
    exact mul_mem (inv_mem (hs.A_le_S1 hII hq hrec ha₀)) hy
  have hP₂ := (hs.cases8_aux hII hq hrec hP8).1
  have hP32 : Nat.card ↥(Pz S z) = 32 := by
    have := hs.card_P hII
    rw [hP8, hP₂] at this
    omega
  have hconj : IsConj z δ := hs.isConj_of_y hII h31 hS128 hP32 hδS hδS1 hδ2 hyS hyS1 hya
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hδ1 : δ ≠ 1 := fun e => hδS1 (e ▸ one_mem _)
  have hδo : orderOf δ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hδ2) hδ1
  have hInt : Interchanges δ K₁ K₂ := hs.swap_of_not_mem hII hδS hδS1
  have hint := (h41 G z S K₁ K₂ hs.fused.std).2.2 δ (hs.S_le_C hII hδS) hconj hInt c⁻¹
    (by rw [inv_inv]; exact hc)
  have hδu : δ * u * δ⁻¹ = u := (P1 u (hUA hs.u_mem)).2 (hs.four_sq u hs.u_mem)
  obtain ⟨k₀, hk₀, hu₀U, hu₀1, hu₀z⟩ := hs.exists_diag' hII hq hδS hδS1 hδ2 hδu
  have hu₀Λ := hbal hδS hδo hInt hc k₀ hk₀
  have hz := hs.z_mem_Lambda hII hc hδh.symm hu₀U hu₀1 hu₀z hu₀Λ
  exact hs.false_of_z_mem_Lambda hII hint hz

end Setup8

theorem lemma_8_5_of_closed (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) (h41 : Prop4_1) (h327 : IG_3_27) (hF : FStar_C) : Lemma8_5 := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h hs hP8 hS7
  by_contra hne
  push Not at hne
  exact hs.lemma85_false' hII hq hrec h31 h41
    (fun hdS hd2 hint hc => hs.balance85 hII h327 hF hdS hd2 hint hc) hP8 hS7 (fun w hw => by
      have := hne w hw
      rwa [commutatorElement_def] at this)



end CFSG.GH74.GLS.Stage1.Thm3.Sec8
