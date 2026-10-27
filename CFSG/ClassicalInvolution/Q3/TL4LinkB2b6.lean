module

public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b3
public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b4
public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem inf_eq_of_isSylow2In {A Q S : Subgroup G} (hQ : IsSylow2In Q A) (hQS : Q ≤ S)
    (hS : IsPGroup 2 S) : A ⊓ S = Q :=
  hQ.eq_of_le (hS.to_le inf_le_right) inf_le_left (le_inf hQ.1 hQS)

private theorem mem_normalizer_of_isSylow2In {A Q S : Subgroup G} (hQ : IsSylow2In Q A)
    (hQS : Q ≤ S) (hS : IsPGroup 2 S) {v : G} (hvS : v ∈ S)
    (hvA : v ∈ Subgroup.normalizer (A : Set G)) : v ∈ Subgroup.normalizer (Q : Set G) := by
  have hAS := inf_eq_of_isSylow2In hQ hQS hS
  rw [Subgroup.mem_normalizer_iff] at hvA ⊢
  intro w
  rw [← hAS, Subgroup.mem_inf, Subgroup.mem_inf, hvA w]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, S.mul_mem (S.mul_mem hvS h2) (S.inv_mem hvS)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := S.mul_mem (S.mul_mem (S.inv_mem hvS) h2) hvS
    rwa [show v⁻¹ * (v * w * v⁻¹) * v = w by group] at this

private theorem conj_mul_of_commute {d e w : G} (h : w * e = e * w) :
    d * e * w * (d * e)⁻¹ = d * w * d⁻¹ := by
  calc d * e * w * (d * e)⁻¹ = d * (e * w) * e⁻¹ * d⁻¹ := by group
    _ = d * (w * e) * e⁻¹ * d⁻¹ := by rw [h]
    _ = d * w * d⁻¹ := by group

private theorem mem_centralizer_of_conj_eq {Q : Subgroup G} {a c : G} (hac : a * c = c * a)
    (h : ∀ w ∈ Q, a * w * a⁻¹ = c * w * c⁻¹) : a * c⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have e1 := h w hw
  have e2 : a * c⁻¹ = c⁻¹ * a := (Commute.inv_right (show Commute a c from hac)).eq
  calc w * (a * c⁻¹) = w * (c⁻¹ * a) := by rw [e2]
    _ = c⁻¹ * (c * w * c⁻¹) * a := by group
    _ = c⁻¹ * (a * w * a⁻¹) * a := by rw [e1]
    _ = c⁻¹ * a * w := by group
    _ = a * c⁻¹ * w := by rw [e2]

private theorem conjSub_inf_centralizer_singleton (g a : G) (B : Subgroup G) :
    conjSub g (B ⊓ Subgroup.centralizer ({a} : Set G)) =
      conjSub g B ⊓ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun _ => ⟨fun h2 => ?_, fun h2 => ?_⟩
  · calc x * (g * a * g⁻¹) = g * (g⁻¹ * x * g * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
      _ = g * a * g⁻¹ * x := by group
  · calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹ * x) * g := by rw [h2]
      _ = a * (g⁻¹ * x * g) := by group

namespace Tri

variable {K J M : Subgroup G} {t u : G}

private theorem mem_E_of_centralizes (h : Tri r Ω K J M t u) {A : Subgroup G}
    (hA : A = K ∨ A = J ∨ A = M) {a : G} (ha : IsUniqueInvolution A a) (hta : t * a = a * t)
    (hua : u * a = a * u) {B Q : Subgroup G} (hB : B ∈ Ω) {b : G}
    (hb : IsUniqueInvolution B b) (hQ : IsSylow2In Q B) {S : Subgroup G} (hS : IsPGroup 2 S)
    (htS : t ∈ S) (huS : u ∈ S) (hQS : Q ≤ S) (hba : b ≠ a) (hc : ∀ w ∈ Q, a * w = w * a) :
    b ∈ Subgroup.closure ({t, u} : Set G) := by
  have hAΩ : A ∈ Ω := by
    rcases hA with rfl | rfl | rfl
    exacts [h.mem, h.adj_J.1, h.adj_M.1]
  have hbQ : b ∈ Q := T3.mem_of_isPGroup hb hQ.1 hQ.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet h.fam.hyp (mem_RSet_of_isSylow2In hB hQ)
    omega)
  have hQa : Q ≤ Subgroup.centralizer ({a} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc w hw).symm
  have hBA : B ∈ omegaNbr Ω A := ⟨hB, fun e => hba (by subst e; exact hb.eq ha), Q,
    mem_RSet_of_isSylow2In hB hQ, hQ.1, hQa.trans (h.fam.tight A hAΩ a ha)⟩
  exact h.mem_E_of_adj hA ha hBA hb (hS.to_le inf_le_left) inf_le_right
    (Subgroup.mem_inf.mpr ⟨htS, Subgroup.mem_centralizer_singleton_iff.mpr hta⟩)
    (Subgroup.mem_inf.mpr ⟨huS, Subgroup.mem_centralizer_singleton_iff.mpr hua⟩)
    (Subgroup.mem_inf.mpr ⟨hQS hbQ, hQa hbQ⟩)

private theorem exists_sylowTri_first (h : Tri r Ω K J M t u) (S' : Sylow 2 G)
    {L A : Subgroup G} (hL : L ∈ Ω) {y : G} (hy : IsUniqueInvolution L y)
    (hA : IsSylow2In A L) (hAS : A ≤ (S' : Subgroup G)) :
    ∃ (J' M' P' T' T'' : Subgroup G) (y₂ : G), SylowTri Ω S' L J' M' P' T' T'' y y₂ := by
  obtain ⟨g, P, T, T', hs⟩ := h.sylowTri_of_sylow S'
  rcases hs.eq_of_sylow h.fam.hyp hL hA hAS with rfl | rfl | rfl
  · have e := hs.inv_K.eq hy
    rw [e] at hs
    exact ⟨_, _, _, _, _, _, hs⟩
  · have hs' := hs.rot
    have e := hs'.inv_K.eq hy
    rw [e] at hs'
    exact ⟨_, _, _, _, _, _, hs'⟩
  · have hs' := hs.rot.rot
    have e := hs'.inv_K.eq hy
    rw [e] at hs'
    exact ⟨_, _, _, _, _, _, hs'⟩

theorem mirror (h : Tri r Ω K J M t u) {W : Subgroup G} (hW2 : IsPGroup 2 W)
    (hWab : IsMulCommutative W) {L : Subgroup G} (hL : L ∈ Ω) {y : G}
    (hy : IsUniqueInvolution L y) (hLW : L ⊓ W ∈ USet Ω) (hKW : K ⊓ W ∈ USet Ω)
    (hJW : J ⊓ W ∈ USet Ω) (hyE : y ∉ Subgroup.closure ({t, u} : Set G)) :
    ∃ (S' : Sylow 2 G) (J' M' P' T' T'' : Subgroup G) (y₂ : G),
      SylowTri Ω S' L J' M' P' T' T'' y y₂ ∧
      Subgroup.closure ({t, u} : Set G) ≤ (S' : Subgroup G) ∧
      2 < Nat.card ↥(K ⊓ (S' : Subgroup G)) ∧ 2 < Nat.card ↥(J ⊓ (S' : Subgroup G)) ∧
      t ∉ Subgroup.closure ({y, y₂} : Set G) ∧ u ∉ Subgroup.closure ({y, y₂} : Set G) ∧
      t * u ∉ Subgroup.closure ({y, y₂} : Set G) := by
  have hΩ := h.fam.hyp
  haveI := hWab
  have hcomm : ∀ {a b : G}, a ∈ W → b ∈ W → a * b = b * a := fun ha hb =>
    Subgroup.mul_comm_of_mem_isMulCommutative W ha hb
  have key : ∀ {A : Subgroup G} {a : G}, IsUniqueInvolution A a → A ⊓ W ∈ USet Ω →
      a ∈ W ∧ 4 ≤ Nat.card ↥(A ⊓ W) := by
    intro A a ha hAW
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hAW
    exact ⟨(Subgroup.mem_inf.mp (T3.mem_of_isPGroup ha inf_le_left
      (Sec6Gen.isPGroup_of_mem_USet hΩ hAW) (by omega))).2, h4⟩
  obtain ⟨htW, hK4⟩ := key h.inv_K hKW
  obtain ⟨huW, hJ4⟩ := key h.inv_J hJW
  obtain ⟨hyW, -⟩ := key hy hLW
  have hWc : W ⊔ W ≤ Subgroup.centralizer
      ((Subgroup.closure ({y} : Set G) : Subgroup G) : Set G) := by
    rw [sup_idem, Subgroup.centralizer_closure]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm hw hyW)
  obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow hW2
  obtain ⟨S', hWS', -, hfc⟩ := Asc77.E187C.exists_sylow_inf_centralizer hS₀ hS₀ hWc
  rw [Subgroup.centralizer_closure] at hfc
  obtain ⟨A, hA, hAS⟩ := exists_sylow_le_of_fullyCentralized h.fam hL hy hfc
  obtain ⟨J', M', P', T', T'', y₂, hs⟩ := h.exists_sylowTri_first S' hL hy hA hAS
  have hyy₂ : y * y₂ = y₂ * y := by
    have e1 : (y * y₂)⁻¹ = y * y₂ := inv_eq_of_mul_eq_one_right hs.inv_M.sq
    rw [← e1, mul_inv_rev, inv_eq_of_mul_eq_one_right hs.inv_K.sq,
      inv_eq_of_mul_eq_one_right hs.inv_J.sq]
  have hadj := hs.adj h.fam
  have hnot : ∀ {A : Subgroup G} {a : G}, (A = K ∨ A = J ∨ A = M) → IsUniqueInvolution A a →
      a ∈ Subgroup.closure ({t, u} : Set G) → a ∈ W → a ∉ Subgroup.closure ({y, y₂} : Set G) := by
    intro A a hA ha haE haW hmem
    have hAΩ : A ∈ Ω := by
      rcases hA with rfl | rfl | rfl
      exacts [h.mem, h.adj_J.1, h.adj_M.1]
    have hfin : ∀ {B : Subgroup G}, B ∈ omegaNbr Ω L → IsUniqueInvolution B a → False := by
      intro B hB hBa
      have hBA : B = A := h.fam.noTwins A hAΩ B ⟨hB.1, a, ha, hBa⟩
      rw [hBA] at hB
      have hLA : L ∈ omegaNbr Ω A := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hL hAΩ hB
      exact hyE (h.mem_E_of_adj hA ha hLA hy hW2
        (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm hw haW)) htW huW hyW)
    rcases TypeCSetup.mem_closure_pair hs.inv_K.sq hs.inv_J.sq hyy₂ hmem with e | e | e | e
    · exact ha.ne_one e
    · exact hyE (e ▸ haE)
    · exact hfin hadj.1 (by rw [e]; exact hs.inv_J)
    · exact hfin hadj.2.1 (by rw [e]; exact hs.inv_M)
  refine ⟨S', J', M', P', T', T'', y₂, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact hWS' htW
    · rw [Set.mem_singleton_iff.mp hx]; exact hWS' huW
  · have := Subgroup.card_le_of_le (inf_le_inf_left K hWS')
    omega
  · have := Subgroup.card_le_of_le (inf_le_inf_left J hWS')
    omega
  · exact hnot (Or.inl rfl) h.inv_K (Subgroup.subset_closure (by simp)) htW
  · exact hnot (Or.inr (Or.inl rfl)) h.inv_J (Subgroup.subset_closure (by simp)) huW
  · exact hnot (Or.inr (Or.inr rfl)) h.inv_M (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) (W.mul_mem htW huW)

theorem no_double_triangle (hQ : QuatAutFacts r) (h : Tri r Ω K J M t u) (hr : RigidEdge K J t u)
    {S' : Sylow 2 G} {L J' M' P' T' T'' : Subgroup G} {y y₂ : G}
    (hs : SylowTri Ω S' L J' M' P' T' T'' y y₂)
    (hE : Subgroup.closure ({t, u} : Set G) ≤ (S' : Subgroup G))
    (hK : 2 < Nat.card ↥(K ⊓ (S' : Subgroup G))) (hJ : 2 < Nat.card ↥(J ⊓ (S' : Subgroup G)))
    (ht : t ∉ Subgroup.closure ({y, y₂} : Set G)) (hu : u ∉ Subgroup.closure ({y, y₂} : Set G))
    (htu : t * u ∉ Subgroup.closure ({y, y₂} : Set G)) : False := by
  have hΩ := h.fam.hyp
  have hS2 : IsPGroup 2 ↥(S' : Subgroup G) := S'.isPGroup'
  have htS : t ∈ (S' : Subgroup G) := hE (Subgroup.subset_closure (by simp))
  have huS : u ∈ (S' : Subgroup G) := hE (Subgroup.subset_closure (by simp))
  obtain ⟨W, hWS, hWab, hW⟩ := exists_frameW hΩ S'
  haveI := hWab
  have hcomm : ∀ {a b : G}, a ∈ W → b ∈ W → a * b = b * a := fun ha hb =>
    Subgroup.mul_comm_of_mem_isMulCommutative W ha hb
  have mem : ∀ {A : Subgroup G} {x : G}, A ⊓ W = Subgroup.zpowers x → x ∈ A ∧ x ∈ W :=
    fun hx => Subgroup.mem_inf.mp (by rw [hx]; exact Subgroup.mem_zpowers _)
  obtain ⟨x₁, hx₁, -, hx₁t⟩ := exists_gen_of_mem_USet h.fam h.mem h.inv_K
    (hW K h.mem hK) inf_le_left
  obtain ⟨x₂, hx₂, -, hx₂u⟩ := exists_gen_of_mem_USet h.fam h.adj_J.1 h.inv_J
    (hW J h.adj_J.1 hJ) inf_le_left
  obtain ⟨a₁, ha₁, ho₁, ha₁y⟩ := exists_gen_of_mem_USet h.fam hs.mem_K hs.inv_K
    (hW L hs.mem_K (two_lt_card_inf_of_sylow h.fam hs.mem_K hs.syl_P hs.le_P)) inf_le_left
  obtain ⟨a₂, ha₂, ho₂, ha₂y⟩ := exists_gen_of_mem_USet h.fam hs.mem_J hs.inv_J
    (hW J' hs.mem_J (two_lt_card_inf_of_sylow h.fam hs.mem_J hs.syl_T hs.le_T)) inf_le_left
  obtain ⟨a₃, ha₃, -, ha₃y⟩ := exists_gen_of_mem_USet h.fam hs.mem_M hs.inv_M
    (hW M' hs.mem_M (two_lt_card_inf_of_sylow h.fam hs.mem_M hs.syl_T' hs.le_T')) inf_le_left
  have hx₁W := (mem hx₁).2
  have hx₂W := (mem hx₂).2
  have ha₁W := (mem ha₁).2
  have ha₂W := (mem ha₂).2
  have ha₃W := (mem ha₃).2
  have huW : u ∈ W := hx₂u ▸ W.pow_mem hx₂W _
  have hyW : y ∈ W := ha₁y ▸ W.pow_mem ha₁W _
  have hy₂W : y₂ ∈ W := ha₂y ▸ W.pow_mem ha₂W _
  have ha₁P : a₁ ∈ P' := by
    rw [← inf_eq_of_isSylow2In hs.syl_P hs.le_P hS2]
    exact Subgroup.mem_inf.mpr ⟨(mem ha₁).1, hWS ha₁W⟩
  have ha₂T : a₂ ∈ T' := by
    rw [← inf_eq_of_isSylow2In hs.syl_T hs.le_T hS2]
    exact Subgroup.mem_inf.mpr ⟨(mem ha₂).1, hWS ha₂W⟩
  have ha₃T : a₃ ∈ T'' := by
    rw [← inf_eq_of_isSylow2In hs.syl_T' hs.le_T' hS2]
    exact Subgroup.mem_inf.mpr ⟨(mem ha₃).1, hWS ha₃W⟩
  have hnorm : ∀ {A Q : Subgroup G} {b : G}, A ∈ Ω → IsUniqueInvolution A b → IsSylow2In Q A →
      Q ≤ (S' : Subgroup G) → b ∈ W → ∀ {v : G}, v ∈ W →
        v ∈ Subgroup.normalizer (Q : Set G) :=
    fun hA hb hQ hQS hbW _ hv => mem_normalizer_of_isSylow2In hQ hQS hS2 (hWS hv)
      (h.fam.tight _ hA _ hb (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm hv hbW)))
  obtain ⟨c, hc⟩ : ∃ c : G, c = a₁ ^ 2 ^ (r - 3) * a₂ ^ 2 ^ (r - 3) * a₃ ^ 2 ^ (r - 3) :=
    ⟨_, rfl⟩
  have hcW : c ∈ W := hc ▸ W.mul_mem (W.mul_mem (W.pow_mem ha₁W _) (W.pow_mem ha₂W _))
    (W.pow_mem ha₃W _)
  have hk2 : 2 ^ (r - 3) * 2 = 2 ^ (r - 2) := by
    have := hQ.three_le
    rw [← pow_succ]
    congr 1
    omega
  have hc2 : c * c = 1 := by
    have h12 : Commute (a₁ ^ 2 ^ (r - 3)) (a₂ ^ 2 ^ (r - 3)) :=
      hcomm (W.pow_mem ha₁W _) (W.pow_mem ha₂W _)
    have h123 : Commute (a₁ ^ 2 ^ (r - 3) * a₂ ^ 2 ^ (r - 3)) (a₃ ^ 2 ^ (r - 3)) :=
      hcomm (W.mul_mem (W.pow_mem ha₁W _) (W.pow_mem ha₂W _)) (W.pow_mem ha₃W _)
    rw [← pow_two, hc, h123.mul_pow, h12.mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, hk2, ha₁y,
      ha₂y, ha₃y]
    exact hs.inv_M.sq
  have hrL : RigidEdge L J' y y₂ := h.rigid_of_adj hr hs.mem_K (hs.adj h.fam).1 hs.inv_K hs.inv_J
  have hstep : ∀ {v a : G}, v ∈ W → v ^ 2 ^ (r - 2) = a → a * a = 1 →
      (¬ ∀ w ∈ P', a * w = w * a) → (¬ ∀ w ∈ T', a * w = w * a) →
      a * c⁻¹ ∈ Subgroup.closure ({y, y₂} : Set G) := by
    intro v a hv hva ha2 hncP hncT
    obtain ⟨e₁⟩ := h.fam.quat L hs.mem_K P' hs.syl_P
    obtain ⟨e₂⟩ := h.fam.quat J' hs.mem_J T' hs.syl_T
    have hP := hQ.stab_power_elem e₁ (hnorm hs.mem_K hs.inv_K hs.syl_P hs.le_P hyW hv) ha₁P ho₁
      (hcomm hv ha₁W)
    have hT := hQ.stab_power_elem e₂ (hnorm hs.mem_J hs.inv_J hs.syl_T hs.le_T hy₂W hv) ha₂T ho₂
      (hcomm hv ha₂W)
    rw [hva] at hP hT
    have hactP := hP.resolve_left hncP
    have hactT := hT.resolve_left hncT
    have haW : a ∈ W := hva ▸ W.pow_mem hv _
    have hac : a * c = c * a := hcomm haW hcW
    have hf : a * c⁻¹ ∈ Subgroup.centralizer (P' : Set G) ⊓ Subgroup.centralizer (T' : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨mem_centralizer_of_conj_eq hac fun w hw => ?_,
        mem_centralizer_of_conj_eq hac fun w hw => ?_⟩
      · have h2 : Commute w (a₂ ^ 2 ^ (r - 3)) := hs.comm_PT w hw _ (T'.pow_mem ha₂T _)
        have h3 : Commute w (a₃ ^ 2 ^ (r - 3)) := hs.comm_PT' w hw _ (T''.pow_mem ha₃T _)
        have e : c * w * c⁻¹ = a₁ ^ 2 ^ (r - 3) * w * (a₁ ^ 2 ^ (r - 3))⁻¹ := by
          rw [hc, mul_assoc (a₁ ^ 2 ^ (r - 3)) (a₂ ^ 2 ^ (r - 3)) (a₃ ^ 2 ^ (r - 3))]
          exact conj_mul_of_commute (Commute.mul_right h2 h3).eq
        rw [hactP w hw, e]
      · have h1 : Commute w (a₁ ^ 2 ^ (r - 3)) := (hs.comm_PT _ (P'.pow_mem ha₁P _) w hw).symm
        have h3 : Commute w (a₃ ^ 2 ^ (r - 3)) := hs.comm_TT' w hw _ (T''.pow_mem ha₃T _)
        have h12 : a₁ ^ 2 ^ (r - 3) * a₂ ^ 2 ^ (r - 3) = a₂ ^ 2 ^ (r - 3) * a₁ ^ 2 ^ (r - 3) :=
          hcomm (W.pow_mem ha₁W _) (W.pow_mem ha₂W _)
        have e : c * w * c⁻¹ = a₂ ^ 2 ^ (r - 3) * w * (a₂ ^ 2 ^ (r - 3))⁻¹ := by
          rw [hc, h12, mul_assoc (a₂ ^ 2 ^ (r - 3)) (a₁ ^ 2 ^ (r - 3)) (a₃ ^ 2 ^ (r - 3))]
          exact conj_mul_of_commute (Commute.mul_right h1 h3).eq
        rw [hactT w hw, e]
    have hf2 : a * c⁻¹ * (a * c⁻¹) = 1 := by
      have e : c⁻¹ * a = a * c⁻¹ := hcomm (W.inv_mem hcW) haW
      calc a * c⁻¹ * (a * c⁻¹) = a * (c⁻¹ * a) * c⁻¹ := by group
        _ = a * (a * c⁻¹) * c⁻¹ := by rw [e]
        _ = a * a * (c * c)⁻¹ := by group
        _ = 1 := by rw [ha2, hc2, inv_one, one_mul]
    exact hrL P' T' hs.syl_P hs.syl_T hs.comm_PT _ hf hf2
  have hyY : y ∈ Subgroup.closure ({y, y₂} : Set G) := Subgroup.subset_closure (by simp)
  have hy₂Y : y₂ ∈ Subgroup.closure ({y, y₂} : Set G) := Subgroup.subset_closure (by simp)
  have hEE : ∀ {b : G}, b ∈ Subgroup.closure ({y, y₂} : Set G) → b ≠ 1 →
      b ∉ Subgroup.closure ({t, u} : Set G) := by
    intro b hb hb1 hbE
    rcases TypeCSetup.mem_closure_pair h.inv_K.sq h.inv_J.sq h.comm_tu hbE with e | e | e | e
    · exact hb1 e
    · exact ht (e ▸ hb)
    · exact hu (e ▸ hb)
    · exact htu (e ▸ hb)
  have hyt : y ≠ t := fun e => ht (e ▸ hyY)
  have hyu : y ≠ u := fun e => hu (e ▸ hyY)
  have hy₂t : y₂ ≠ t := fun e => ht (e ▸ hy₂Y)
  have hy₂u : y₂ ≠ u := fun e => hu (e ▸ hy₂Y)
  have hft := hstep hx₁W hx₁t h.inv_K.sq
    (fun hc => hEE hyY hs.inv_K.ne_one (h.mem_E_of_centralizes (Or.inl rfl) h.inv_K rfl
      h.comm_tu.symm hs.mem_K hs.inv_K hs.syl_P hS2 htS huS hs.le_P hyt hc))
    (fun hc => hEE hy₂Y hs.inv_J.ne_one (h.mem_E_of_centralizes (Or.inl rfl) h.inv_K rfl
      h.comm_tu.symm hs.mem_J hs.inv_J hs.syl_T hS2 htS huS hs.le_T hy₂t hc))
  have hfu := hstep hx₂W hx₂u h.inv_J.sq
    (fun hc => hEE hyY hs.inv_K.ne_one (h.mem_E_of_centralizes (Or.inr (Or.inl rfl)) h.inv_J
      h.comm_tu rfl hs.mem_K hs.inv_K hs.syl_P hS2 htS huS hs.le_P hyu hc))
    (fun hc => hEE hy₂Y hs.inv_J.ne_one (h.mem_E_of_centralizes (Or.inr (Or.inl rfl)) h.inv_J
      h.comm_tu rfl hs.mem_J hs.inv_J hs.syl_T hS2 htS huS hs.le_T hy₂u hc))
  apply htu
  have e : t * u = t * c⁻¹ * (u * c⁻¹) := by
    have h1 : c⁻¹ * u = u * c⁻¹ := hcomm (W.inv_mem hcW) huW
    calc t * u = t * u * (c * c)⁻¹ := by rw [hc2, inv_one, mul_one]
      _ = t * (c⁻¹ * u) * c⁻¹ := by rw [h1]; group
      _ = t * c⁻¹ * (u * c⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hft hfu

theorem no_type3_normalized (hQ : QuatAutFacts r) (h : Tri r Ω K J M t u) (hr : RigidEdge K J t u)
    {S : Sylow 2 G} {P T T' : Subgroup G} (hs : SylowTri Ω S K J M P T T' t u) {L : Subgroup G}
    (hL : L ∈ Ω) {y : G} (hy : IsUniqueInvolution L y)
    (hyE : y ∉ Subgroup.closure ({t, u} : Set G))
    (hLS : 2 < Nat.card ↥(L ⊓ (S : Subgroup G))) : False := by
  obtain ⟨W, hWS, hWab, hW⟩ := exists_frameW h.fam.hyp S
  have hKS := two_lt_card_inf_of_sylow h.fam h.mem hs.syl_P hs.le_P
  have hJS := two_lt_card_inf_of_sylow h.fam hs.mem_J hs.syl_T hs.le_T
  obtain ⟨S', J', M', P', T', T'', y₂, hs', hE, hK, hJ, ht, hu, htu⟩ :=
    h.mirror (S.isPGroup'.to_le hWS) hWab hL hy (hW L hL hLS) (hW K h.mem hKS)
      (hW J hs.mem_J hJS) hyE
  exact h.no_double_triangle hQ hr hs' hE hK hJ ht hu htu

private theorem no_type3_std (hQ : QuatAutFacts r) (h : Tri r Ω K J M t u)
    (hr : RigidEdge K J t u) {S : Sylow 2 G} {P T T' : Subgroup G}
    (hs : SylowTri Ω S K J M P T T' t u) {L : Subgroup G} (hL : L ∈ Ω) {y : G}
    (hy : IsUniqueInvolution L y) (hyt : y ≠ t) {V : Subgroup G}
    (hV : IsSylow2In V (L ⊓ Subgroup.centralizer ({t} : Set G))) (hVU : V ∈ USet Ω)
    (hVS : V ≤ (S : Subgroup G)) : False := by
  have hΩ := h.fam.hyp
  obtain ⟨R₀, -, J₀, hJ₀, hR₀, -, -, hR₀V, hV4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
  have htP : t ∈ P := T3.mem_of_isPGroup h.inv_K hs.syl_P.1 hs.syl_P.2.1 (by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.mem hs.syl_P)
    omega)
  have hne : ∀ {B Q : Subgroup G}, B ∈ Ω → IsSylow2In Q B → (∀ x ∈ Q, x * t = t * x) →
      L ≠ B := by
    intro B Q hB hQ hQt hLB
    subst hLB
    have hle := hV.natCard_le hQ.2.1 (le_inf hQ.1 fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hQt x hx))
    have := hΩ.omega3 J₀ hJ₀ _ hB R₀ Q hR₀ hQ
    omega
  have hyE : y ∉ Subgroup.closure ({t, u} : Set G) := by
    intro hyE
    rcases TypeCSetup.mem_closure_pair h.inv_K.sq h.inv_J.sq h.comm_tu hyE with e | e | e | e
    · exact hy.ne_one e
    · exact hyt e
    · exact hne hs.mem_J hs.syl_T (fun x hx => (hs.comm_PT t htP x hx).symm)
        (h.fam.noTwins J hs.mem_J L ⟨hL, u, h.inv_J, e ▸ hy⟩)
    · exact hne hs.mem_M hs.syl_T' (fun x hx => (hs.comm_PT' t htP x hx).symm)
        (h.fam.noTwins M hs.mem_M L ⟨hL, t * u, h.inv_M, e ▸ hy⟩)
  have hLS : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf (hV.1.trans inf_le_left) hVS)
    omega
  exact h.no_type3_normalized hQ hr hs hL hy hyE hLS

theorem no_type3 (hQ : QuatAutFacts r) (h : Tri r Ω K J M t u) (hr : RigidEdge K J t u)
    {A B : Subgroup G} (hA : A ∈ Ω) (hB : B ∈ Ω) {a b : G} (ha : IsUniqueInvolution A a)
    (hb : IsUniqueInvolution B b) (hne : a ≠ b) {V : Subgroup G}
    (hV : IsSylow2In V (B ⊓ Subgroup.centralizer ({a} : Set G))) (hbV : b ∈ V)
    (hVU : V ∈ USet Ω) : False := by
  have hci := h.fam.hyp.conjInvariant
  obtain ⟨S, P, T, T', hs, hfc⟩ := h.exists_std_sylowTri
  obtain ⟨g, hg⟩ := h.trans A hA K h.mem
  have hga : g * a * g⁻¹ = t := by
    have := ha.conj g
    rw [hg] at this
    exact (h.inv_K.eq this).symm
  have hVg : IsSylow2In (conjSub g V) (conjSub g B ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have := hV.conj g
    rwa [conjSub_inf_centralizer_singleton, hga] at this
  obtain ⟨d, hd, hdV⟩ := Sec7.exists_conj_le_of_isSylow2In hfc hVg.2.1 (hVg.1.trans inf_le_right)
  have hdt : d⁻¹ * t * d⁻¹⁻¹ = t := by
    have e : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hd
    calc d⁻¹ * t * d⁻¹⁻¹ = d⁻¹ * (t * d) := by group
      _ = d⁻¹ * (d * t) := by rw [e]
      _ = t := by group
  have hV' := hVg.conj d⁻¹
  rw [conjSub_inf_centralizer_singleton, hdt] at hV'
  have hyt : d⁻¹ * (g * b * g⁻¹) * d⁻¹⁻¹ ≠ t := by
    intro e
    apply hne
    have e2 : d⁻¹ * (g * b * g⁻¹) * d⁻¹⁻¹ = d⁻¹ * (g * a * g⁻¹) * d⁻¹⁻¹ := by rw [e, hga, hdt]
    have e3 := mul_left_cancel (mul_right_cancel e2)
    exact (mul_left_cancel (mul_right_cancel e3)).symm
  have hVS : conjSub d⁻¹ (conjSub g V) ≤ (S : Subgroup G) := by
    refine le_trans (b := (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)) ?_ inf_le_left
    rw [conjSub_le_iff, inv_inv]
    exact hdV
  exact no_type3_std hQ h hr hs (hci d⁻¹ _ (hci g B hB)) ((hb.conj g).conj d⁻¹) hyt hV'
    (USet.conj hci (USet.conj hci hVU g) d⁻¹) hVS

end Tri

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
