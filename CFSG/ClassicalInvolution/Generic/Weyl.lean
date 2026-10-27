module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.Open.FischerExistenceUniquenessMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.Generic

open scoped MatrixGroups
open CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {F : Type*} [Field F] {G : Type*} [Group G]

namespace ToralFrame

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

@[expose] def permOf (Fr : ToralFrame F Ω E S) (n : Subgroup.normalizer (E : Set G)) : Equiv.Perm ↥S where
  toFun K := ⟨conjSub (n : G) K, Fr.conj_mem n.2 K.2⟩
  invFun K := ⟨conjSub (n : G)⁻¹ K, Fr.conj_mem ((Subgroup.normalizer (E : Set G)).inv_mem n.2) K.2⟩
  left_inv _ := Subtype.ext (conjSub_inv_conjSub _ _)
  right_inv _ := Subtype.ext (conjSub_conjSub_inv _ _)

@[expose] def act (Fr : ToralFrame F Ω E S) : Subgroup.normalizer (E : Set G) →* Equiv.Perm ↥S where
  toFun := Fr.permOf
  map_one' := Equiv.ext fun K => Subtype.ext (conjSub_one (K : Subgroup G))
  map_mul' a b := Equiv.ext fun K => Subtype.ext (conjSub_mul (a : G) (b : G) (K : Subgroup G))

variable (Fr : ToralFrame F Ω E S)

theorem coe_act_apply (n : Subgroup.normalizer (E : Set G)) (K : ↥S) :
    ((Fr.act n K : ↥S) : Subgroup G) = conjSub (n : G) (K : Subgroup G) := rfl

theorem act_apply_eq_iff {n : Subgroup.normalizer (E : Set G)} {K L : ↥S} :
    Fr.act n K = L ↔ conjSub (n : G) (K : Subgroup G) = L :=
  Subtype.ext_iff

theorem act_eq_one_of_forall {n : Subgroup.normalizer (E : Set G)}
    (h : ∀ K ∈ S, conjSub (n : G) K = K) : Fr.act n = 1 :=
  Equiv.ext fun K => Subtype.ext (h K K.2)

theorem conjSub_eq_of_act_eq_one {n : Subgroup.normalizer (E : Set G)} (h : Fr.act n = 1)
    {K : Subgroup G} (hK : K ∈ S) : conjSub (n : G) K = K := by
  exact congrArg (fun π : Equiv.Perm ↥S => ((π ⟨K, hK⟩ : ↥S) : Subgroup G)) h

theorem act_of_mem {e : G} (he : e ∈ E) : Fr.act ⟨e, Subgroup.le_normalizer he⟩ = 1 :=
  Fr.act_eq_one_of_forall fun _ hK => (Fr.inSigma hK).conjSub_eq he

@[expose] def kerG : Subgroup G := Fr.act.ker.map (Subgroup.normalizer (E : Set G)).subtype

theorem mem_kerG_iff {x : G} :
    x ∈ Fr.kerG ↔ ∃ h : x ∈ Subgroup.normalizer (E : Set G), Fr.act ⟨x, h⟩ = 1 := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨h, h1⟩
    exact ⟨⟨x, h⟩, h1, rfl⟩

end ToralFrame

structure IsLine (E : Subgroup G) (K L : Subgroup G) : Prop where
  torus_left : ∀ c ∈ centPart K E, conjSub c L = L
  torus_right : ∀ c ∈ centPart L E, conjSub c K = K
  swap : ∃ wK ∈ normPart K E, wK ∉ centPart K E ∧ ∃ wL ∈ normPart L E, wL ∉ centPart L E ∧
    conjSub wK L = conjSub wL K ∧ (wK * wL) ^ 3 ∈ centPart K E ⊔ centPart L E

@[expose] def A2Dichotomy (E : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ IsLine E K L

@[expose] def CentTrivial (E : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ K ∈ S, ∀ c ∈ centPart K E, ∀ L ∈ S, conjSub c L = L

@[expose] def FibreLE2 (S : Set (Subgroup G)) : Prop :=
  ∀ (z : G), ∀ K ∈ S, ∀ L ∈ S, ∀ M ∈ S, IsUniqueInvolution K z → IsUniqueInvolution L z →
    IsUniqueInvolution M z → K = L ∨ K = M ∨ L = M

@[expose] def weylN (E : Subgroup G) (S : Set (Subgroup G)) : Subgroup (Subgroup.normalizer (E : Set G)) :=
  Subgroup.closure {n | ∃ K ∈ S, (n : G) ∈ normPart K E}

theorem A2Dichotomy.centTrivial {E : Subgroup G} {S : Set (Subgroup G)} (hA2 : A2Dichotomy E S) :
    CentTrivial E S := by
  intro K hK c hc L hL
  by_cases hKL : K = L
  · subst hKL
    exact conjSub_eq_self_of_mem (centPart_le_left _ _ hc)
  · rcases hA2 K hK L hL hKL with h | h
    · exact conjSub_eq_of_mem_of_commutes (centPart_le_left _ _ hc) h
    · exact h.torus_left c hc

theorem braid_conj_aux {H : Type*} [Group H] {a b : H} (ha : a * a = 1) (hb : b * b = 1)
    (h : b * a * b = a * b * a) : a * b * a * (a * b)⁻¹ = b := by
  have : (a * b)⁻¹ = b * a := by
    rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
  rw [this]
  calc a * b * a * (b * a) = (a * b * a) * b * a := by group
    _ = (b * a * b) * b * a := by rw [← h]
    _ = b * a * (b * b) * a := by group
    _ = b := by rw [hb, mul_one, mul_assoc, ha, mul_one]

namespace ToralFrame

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}
variable (Fr : ToralFrame F Ω E S)
include Fr

theorem centPart_le_kerG (hT : CentTrivial E S) {K : Subgroup G} (hK : K ∈ S) :
    centPart K E ≤ Fr.kerG := by
  intro c hc
  have hcN : c ∈ Subgroup.normalizer (E : Set G) :=
    (mem_normPart_iff.mp (centPart_le_normPart K E hc)).2
  refine Fr.mem_kerG_iff.mpr ⟨hcN, ?_⟩
  exact Fr.act_eq_one_of_forall fun L hL => hT K hK c hc L hL

variable [Finite F]

theorem exists_w (K : ↥S) :
    ∃ w, w ∈ normPart (K : Subgroup G) E ∧ w ∉ centPart (K : Subgroup G) E :=
  (Fr.inSigma K.2).exists_mem_normPart_not_mem_centPart Fr.odd Fr.five

noncomputable def w (K : ↥S) : G := Classical.choose (Fr.exists_w K)

theorem w_mem (K : ↥S) : Fr.w K ∈ normPart (K : Subgroup G) E :=
  (Classical.choose_spec (Fr.exists_w K)).1

theorem w_not_mem (K : ↥S) : Fr.w K ∉ centPart (K : Subgroup G) E :=
  (Classical.choose_spec (Fr.exists_w K)).2

theorem w_mem_normalizer (K : ↥S) : Fr.w K ∈ Subgroup.normalizer (E : Set G) :=
  (mem_normPart_iff.mp (Fr.w_mem K)).2

@[expose] noncomputable def rho (K : ↥S) : Equiv.Perm ↥S := Fr.act ⟨Fr.w K, Fr.w_mem_normalizer K⟩

theorem act_eq_rho (hT : CentTrivial E S) {K : ↥S} {w : G} (hw : w ∈ normPart (K : Subgroup G) E)
    (hw' : w ∉ centPart (K : Subgroup G) E) :
    Fr.act ⟨w, (mem_normPart_iff.mp hw).2⟩ = Fr.rho K := by
  have hc := (Fr.inSigma K.2).inv_mul_mem_centPart Fr.odd (Fr.w_mem K) (Fr.w_not_mem K) hw hw'
  obtain ⟨h, h1⟩ := Fr.mem_kerG_iff.mp (Fr.centPart_le_kerG hT K.2 hc)
  have h2 : (⟨w, (mem_normPart_iff.mp hw).2⟩ : Subgroup.normalizer (E : Set G)) =
      ⟨Fr.w K, Fr.w_mem_normalizer K⟩ * ⟨(Fr.w K)⁻¹ * w, h⟩ :=
    Subtype.ext (by simp)
  rw [h2, map_mul, h1, mul_one]
  rfl

theorem rho_apply_self (K : ↥S) : Fr.rho K K = K :=
  Subtype.ext (conjSub_eq_self_of_mem (normPart_le_left _ _ (Fr.w_mem K)))

theorem rho_apply_of_commutes {K L : ↥S} (h : Commutes (K : Subgroup G) (L : Subgroup G)) :
    Fr.rho K L = L :=
  Subtype.ext (conjSub_eq_of_mem_of_commutes (normPart_le_left _ _ (Fr.w_mem K)) h)

theorem rho_mul_self (K : ↥S) : Fr.rho K * Fr.rho K = 1 := by
  obtain ⟨z, hz⟩ := Fr.exists_isUniqueInvolution K.2
  have hzE : z ∈ E := Fr.mem_of_isUniqueInvolution K.2 hz
  have hw := (Fr.inSigma K.2).sq_eq_of_mem Fr.odd hz (Fr.w_mem K) (Fr.w_not_mem K)
  have h1 := Fr.act_of_mem hzE
  rw [rho, ← map_mul]
  convert h1 using 2
  exact Subtype.ext hw

theorem rho_inv (K : ↥S) : (Fr.rho K)⁻¹ = Fr.rho K :=
  inv_eq_of_mul_eq_one_right (Fr.rho_mul_self K)

theorem act_mul_rho_mul_act_inv (hT : CentTrivial E S) (n : Subgroup.normalizer (E : Set G))
    (K : ↥S) : Fr.act n * Fr.rho K * (Fr.act n)⁻¹ = Fr.rho (Fr.act n K) := by
  set K' : ↥S := Fr.act n K with hK'
  have hmem : (n : G) * Fr.w K * (n : G)⁻¹ ∈ normPart (K' : Subgroup G) E := by
    refine mem_normPart_iff.mpr ⟨conj_mem_conjSub (normPart_le_left _ _ (Fr.w_mem K)), ?_⟩
    exact (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).mul_mem n.2 (Fr.w_mem_normalizer K))
      ((Subgroup.normalizer (E : Set G)).inv_mem n.2)
  have hnot : (n : G) * Fr.w K * (n : G)⁻¹ ∉ centPart (K' : Subgroup G) E := by
    intro hc
    apply Fr.w_not_mem K
    rw [mem_centPart_iff] at hc ⊢
    refine ⟨normPart_le_left _ _ (Fr.w_mem K), fun e he => ?_⟩
    have he' : (n : G) * e * (n : G)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp n.2 e).mp he
    have := hc.2 _ he'
    calc e * Fr.w K = (n : G)⁻¹ * (((n : G) * e * (n : G)⁻¹) * ((n : G) * Fr.w K * (n : G)⁻¹)) *
          (n : G) := by group
      _ = (n : G)⁻¹ * (((n : G) * Fr.w K * (n : G)⁻¹) * ((n : G) * e * (n : G)⁻¹)) * (n : G) := by
        rw [this]
      _ = Fr.w K * e := by group
  have h := Fr.act_eq_rho hT hmem hnot
  rw [← h]
  have h3 : (⟨(n : G) * Fr.w K * (n : G)⁻¹, (mem_normPart_iff.mp hmem).2⟩ :
      Subgroup.normalizer (E : Set G)) = n * ⟨Fr.w K, Fr.w_mem_normalizer K⟩ * n⁻¹ :=
    Subtype.ext (by simp)
  rw [h3, map_mul, map_mul, map_inv]
  rfl

theorem rho_mul_rho_mul_rho (hT : CentTrivial E S) (K L : ↥S) :
    Fr.rho L * Fr.rho K * Fr.rho L = Fr.rho (Fr.rho L K) := by
  have h := Fr.act_mul_rho_mul_act_inv hT ⟨Fr.w L, Fr.w_mem_normalizer L⟩ K
  change Fr.rho L * Fr.rho K * (Fr.rho L)⁻¹ = Fr.rho (Fr.rho L K) at h
  rwa [Fr.rho_inv] at h

theorem rho_apply_of_isLine (hT : CentTrivial E S) {K L : ↥S} (hKL : K ≠ L)
    (h : IsLine E (K : Subgroup G) (L : Subgroup G)) :
    Fr.rho K L = Fr.rho L K ∧ Fr.rho K L ≠ K ∧ Fr.rho K L ≠ L ∧
      (Fr.rho K * Fr.rho L) ^ 3 = 1 := by
  obtain ⟨wK, hwK, hwK', wL, hwL, hwL', hswap, hcube⟩ := h.swap
  have hρK := Fr.act_eq_rho hT hwK hwK'
  have hρL := Fr.act_eq_rho hT hwL hwL'
  have hne : (K : Subgroup G) ≠ L := fun h => hKL (Subtype.ext h)
  have e1 : Fr.rho K L = Fr.rho L K := by
    rw [← hρK, ← hρL]
    exact Subtype.ext hswap
  refine ⟨e1, ?_, ?_, ?_⟩
  · intro hc
    rw [← hρK] at hc
    exact conjSub_ne_of_ne (normPart_le_left _ _ hwK) hne (congrArg Subtype.val hc)
  · intro hc
    rw [e1, ← hρL] at hc
    exact conjSub_ne_of_ne (normPart_le_left _ _ hwL) hne.symm (congrArg Subtype.val hc)
  · have hmem : (wK * wL) ^ 3 ∈ Fr.kerG :=
      sup_le (Fr.centPart_le_kerG hT K.2) (Fr.centPart_le_kerG hT L.2) hcube
    obtain ⟨hN, h1⟩ := Fr.mem_kerG_iff.mp hmem
    have h2 : ((⟨wK, (mem_normPart_iff.mp hwK).2⟩ * ⟨wL, (mem_normPart_iff.mp hwL).2⟩ : 
        Subgroup.normalizer (E : Set G)) ^ 3) = ⟨(wK * wL) ^ 3, hN⟩ := Subtype.ext (by simp)
    rw [← hρK, ← hρL, ← map_mul, ← map_pow, h2]
    exact h1

theorem orderOf_rho_mul_rho_of_isLine (hT : CentTrivial E S) {K L : ↥S} (hKL : K ≠ L)
    (h : IsLine E (K : Subgroup G) (L : Subgroup G)) : orderOf (Fr.rho K * Fr.rho L) = 3 := by
  obtain ⟨-, -, h3, h4⟩ := Fr.rho_apply_of_isLine hT hKL h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime h4 fun h1 => h3 ?_
  have h5 : Fr.rho K = Fr.rho L := by
    have := congrArg (· * Fr.rho L) h1
    simpa [mul_assoc, Fr.rho_mul_self] using this
  rw [h5]
  exact Fr.rho_apply_self L

theorem noncomm_rho_apply_left {K L : ↥S} (h : ¬ Commutes (K : Subgroup G) (L : Subgroup G)) :
    ¬ Commutes (K : Subgroup G) (Fr.rho K L : Subgroup G) := by
  intro hc
  apply h
  have hw := normPart_le_left _ _ (Fr.w_mem K)
  have h1 : Commutes (conjSub (Fr.w K) (K : Subgroup G)) (conjSub (Fr.w K) (L : Subgroup G)) := by
    rw [conjSub_eq_self_of_mem hw]
    exact hc
  exact (commutes_conjSub_iff _).mp h1

theorem exists_third_member (hA2 : A2Dichotomy E S) {K L : ↥S} (hKL : K ≠ L)
    (hnc : ¬ Commutes (K : Subgroup G) (L : Subgroup G)) :
    ∃ M : ↥S, Fr.rho K L = M ∧ Fr.rho L K = M ∧ M ≠ K ∧ M ≠ L ∧
      ¬ Commutes (K : Subgroup G) M ∧ ¬ Commutes (L : Subgroup G) M ∧
      orderOf (Fr.rho K * Fr.rho L) = 3 := by
  have hT := hA2.centTrivial
  have hl : IsLine E (K : Subgroup G) (L : Subgroup G) := by
    rcases hA2 K K.2 L L.2 (fun h => hKL (Subtype.ext h)) with h | h
    · exact absurd h hnc
    · exact h
  obtain ⟨e1, e2, e3, -⟩ := Fr.rho_apply_of_isLine hT hKL hl
  refine ⟨Fr.rho K L, rfl, e1.symm, e2, e3, Fr.noncomm_rho_apply_left hnc, ?_,
    Fr.orderOf_rho_mul_rho_of_isLine hT hKL hl⟩
  rw [e1]
  exact Fr.noncomm_rho_apply_left fun h => hnc h.symm

theorem commutes_iff_rho_comm (hA2 : A2Dichotomy E S) {K L : ↥S} (hKL : K ≠ L) :
    Commutes (K : Subgroup G) (L : Subgroup G) ↔ Fr.rho K * Fr.rho L = Fr.rho L * Fr.rho K := by
  have hT := hA2.centTrivial
  constructor
  · intro h
    have hw : Fr.w K * Fr.w L = Fr.w L * Fr.w K :=
      h _ (normPart_le_left _ _ (Fr.w_mem K)) _ (normPart_le_left _ _ (Fr.w_mem L))
    have : (⟨Fr.w K, Fr.w_mem_normalizer K⟩ * ⟨Fr.w L, Fr.w_mem_normalizer L⟩ :
        Subgroup.normalizer (E : Set G)) =
        ⟨Fr.w L, Fr.w_mem_normalizer L⟩ * ⟨Fr.w K, Fr.w_mem_normalizer K⟩ := Subtype.ext hw
    unfold rho
    rw [← map_mul, ← map_mul, this]
  · intro hc
    by_contra hnc
    have hl : IsLine E (K : Subgroup G) (L : Subgroup G) := by
      rcases hA2 K K.2 L L.2 (fun h => hKL (Subtype.ext h)) with h | h
      · exact absurd h hnc
      · exact h
    obtain ⟨e1, e2, -, -⟩ := Fr.rho_apply_of_isLine hT hKL hl
    apply e2
    have h1 := congrArg (fun π : Equiv.Perm ↥S => π L) hc
    simp only [Equiv.Perm.mul_apply, Fr.rho_apply_self] at h1
    have h2 : Fr.rho L (Fr.rho L K) = K := by
      have := congrArg (fun π : Equiv.Perm ↥S => π K) (Fr.rho_mul_self L)
      simpa using this
    calc Fr.rho K L = Fr.rho L (Fr.rho K L) := h1
      _ = Fr.rho L (Fr.rho L K) := by rw [e1]
      _ = K := h2

theorem orderOf_rho_mul_rho_mem (hA2 : A2Dichotomy E S) (K L : ↥S) :
    orderOf (Fr.rho K * Fr.rho L) ∈ ({1, 2, 3} : Set ℕ) := by
  have hT := hA2.centTrivial
  by_cases hKL : K = L
  · subst hKL
    rw [Fr.rho_mul_self, orderOf_one]
    simp
  · have hne : (K : Subgroup G) ≠ L := fun h => hKL (Subtype.ext h)
    by_cases hc : Commutes (K : Subgroup G) (L : Subgroup G)
    · have hcomm : Commute (Fr.rho K) (Fr.rho L) := (Fr.commutes_iff_rho_comm hA2 hKL).mp hc
      have h2 : (Fr.rho K * Fr.rho L) ^ 2 = 1 := by
        rw [hcomm.mul_pow, pow_two, pow_two, Fr.rho_mul_self, Fr.rho_mul_self, mul_one]
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h <;>
        simp [h]
    · have hl : IsLine E (K : Subgroup G) (L : Subgroup G) := by
        rcases hA2 K K.2 L L.2 hne with h | h
        · exact absurd h hc
        · exact h
      simp [Fr.orderOf_rho_mul_rho_of_isLine hT hKL hl]

omit [Finite F] in
theorem exists_neighbor (hconn : NonCommConnected S) (K : ↥S) :
    ∃ L : ↥S, L ≠ K ∧ ¬ Commutes (K : Subgroup G) (L : Subgroup G) := by
  obtain ⟨K₁, hK₁, L₁, hL₁, hne⟩ := Fr.exists_ne
  have : ∃ L₀ : ↥S, L₀ ≠ K := by
    by_cases h : K₁ = (K : Subgroup G)
    · exact ⟨⟨L₁, hL₁⟩, fun hh => hne (h.trans (congrArg Subtype.val hh.symm))⟩
    · exact ⟨⟨K₁, hK₁⟩, fun hh => h (congrArg Subtype.val hh)⟩
  obtain ⟨L₀, hL₀⟩ := this
  obtain ⟨p⟩ := hconn.preconnected K L₀
  cases p with
  | nil => exact absurd rfl hL₀
  | cons h _ =>
    obtain ⟨h1, h2⟩ := nonCommGraph_adj.mp h
    exact ⟨_, h1.symm, h2⟩

theorem rho_ne_one (hA2 : A2Dichotomy E S) (hconn : NonCommConnected S) (K : ↥S) :
    Fr.rho K ≠ 1 := by
  have hT := hA2.centTrivial
  obtain ⟨L, hLK, hnc⟩ := Fr.exists_neighbor hconn K
  have hKL : K ≠ L := hLK.symm
  have hne : (K : Subgroup G) ≠ L := fun h => hKL (Subtype.ext h)
  have hl : IsLine E (K : Subgroup G) (L : Subgroup G) := by
    rcases hA2 K K.2 L L.2 hne with h | h
    · exact absurd h hnc
    · exact h
  obtain ⟨-, -, h3, -⟩ := Fr.rho_apply_of_isLine hT hKL hl
  intro h
  apply h3
  rw [h]
  rfl

@[expose] noncomputable def mu : Subgroup (Equiv.Perm ↥S) := Subgroup.closure (Set.range Fr.rho)

theorem rho_mem_mu (K : ↥S) : Fr.rho K ∈ Fr.mu := Subgroup.subset_closure ⟨K, rfl⟩

@[expose] noncomputable def rhoMu (K : ↥S) : ↥Fr.mu := ⟨Fr.rho K, Fr.rho_mem_mu K⟩

@[simp] theorem coe_rhoMu (K : ↥S) : (Fr.rhoMu K : Equiv.Perm ↥S) = Fr.rho K := rfl

theorem mu_le_range_act : Fr.mu ≤ Fr.act.range := by
  rw [mu, Subgroup.closure_le]
  rintro _ ⟨K, rfl⟩
  exact ⟨_, rfl⟩

theorem isConj_rhoMu_of_adj (hA2 : A2Dichotomy E S) {K L : ↥S} (hKL : K ≠ L)
    (hnc : ¬ Commutes (K : Subgroup G) (L : Subgroup G)) :
    IsConj (Fr.rhoMu K) (Fr.rhoMu L) := by
  have hT := hA2.centTrivial
  have hne : (K : Subgroup G) ≠ L := fun h => hKL (Subtype.ext h)
  have hl : IsLine E (K : Subgroup G) (L : Subgroup G) := by
    rcases hA2 K K.2 L L.2 hne with h | h
    · exact absurd h hnc
    · exact h
  obtain ⟨e1, -, -, -⟩ := Fr.rho_apply_of_isLine hT hKL hl
  have h1 := Fr.act_mul_rho_mul_act_inv hT ⟨Fr.w L, Fr.w_mem_normalizer L⟩ K
  have h2 := Fr.act_mul_rho_mul_act_inv hT ⟨Fr.w K, Fr.w_mem_normalizer K⟩ L
  change Fr.rho L * Fr.rho K * (Fr.rho L)⁻¹ = Fr.rho (Fr.rho L K) at h1
  change Fr.rho K * Fr.rho L * (Fr.rho K)⁻¹ = Fr.rho (Fr.rho K L) at h2
  rw [e1] at h2
  rw [Fr.rho_inv] at h1 h2
  have hB : Fr.rho L * Fr.rho K * Fr.rho L = Fr.rho K * Fr.rho L * Fr.rho K := h1.trans h2.symm
  refine isConj_iff.mpr ⟨Fr.rhoMu K * Fr.rhoMu L, Subtype.ext ?_⟩
  exact braid_conj_aux (Fr.rho_mul_self K) (Fr.rho_mul_self L) hB

theorem isConj_rhoMu (hA2 : A2Dichotomy E S) (hconn : NonCommConnected S) (K L : ↥S) :
    IsConj (Fr.rhoMu K) (Fr.rhoMu L) := by
  obtain ⟨p⟩ := hconn.preconnected K L
  induction p with
  | nil => exact IsConj.refl _
  | cons h _ ih =>
    obtain ⟨h1, h2⟩ := nonCommGraph_adj.mp h
    exact (Fr.isConj_rhoMu_of_adj hA2 h1 h2).trans ih

theorem isPair (hA2 : A2Dichotomy E S) (hconn : NonCommConnected S) :
    CFSG.Open.fischerEUIsPair (Set.range Fr.rhoMu) := by
  have hT := hA2.centTrivial
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨K₀, hK₀, -⟩ := Fr.exists_ne
    refine ⟨Fr.rhoMu ⟨K₀, hK₀⟩, ?_⟩
    ext g
    constructor
    · rintro ⟨K, rfl⟩
      exact Fr.isConj_rhoMu hA2 hconn _ K
    · intro hg
      obtain ⟨c, hc⟩ := isConj_iff.mp hg
      obtain ⟨n, hn⟩ := Fr.mu_le_range_act c.2
      refine ⟨Fr.act n ⟨K₀, hK₀⟩, Subtype.ext ?_⟩
      rw [← hc]
      show Fr.rho (Fr.act n ⟨K₀, hK₀⟩) = (c : Equiv.Perm ↥S) * Fr.rho ⟨K₀, hK₀⟩ * (c : Equiv.Perm ↥S)⁻¹
      rw [← Fr.act_mul_rho_mul_act_inv hT n, hn]
  · rintro _ ⟨K, rfl⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [pow_two] using Fr.rho_mul_self K)
    · intro h
      exact Fr.rho_ne_one hA2 hconn K (congrArg Subtype.val h)
  · rintro _ ⟨K, rfl⟩ _ ⟨L, rfl⟩
    have h := Fr.orderOf_rho_mul_rho_mem hA2 K L
    rw [← Subgroup.orderOf_coe (Fr.rhoMu K * Fr.rhoMu L)]
    exact h
  · have : Set.range Fr.rhoMu = Subtype.val ⁻¹' Set.range Fr.rho := by
      ext g
      constructor
      · rintro ⟨K, rfl⟩
        exact ⟨K, rfl⟩
      · rintro ⟨K, hK⟩
        exact ⟨K, Subtype.ext hK⟩
    rw [this]
    exact Subgroup.closure_closure_coe_preimage

theorem rho_apply_eq_iff (hA2 : A2Dichotomy E S) (K L : ↥S) :
    Fr.rho K L = L ↔ L = K ∨ Commutes (K : Subgroup G) (L : Subgroup G) := by
  have hT := hA2.centTrivial
  constructor
  · intro h
    by_cases hLK : L = K
    · exact Or.inl hLK
    · by_cases hc : Commutes (K : Subgroup G) (L : Subgroup G)
      · exact Or.inr hc
      · exfalso
        have hKL : K ≠ L := fun h => hLK h.symm
        have hl : IsLine E (K : Subgroup G) (L : Subgroup G) := by
          rcases hA2 K K.2 L L.2 (fun h => hKL (Subtype.ext h)) with h | h
          · exact absurd h hc
          · exact h
        exact (Fr.rho_apply_of_isLine hT hKL hl).2.2.1 h
  · rintro (rfl | h)
    · exact Fr.rho_apply_self L
    · exact Fr.rho_apply_of_commutes h

theorem closedNbhd_eq_of_rho_eq (hA2 : A2Dichotomy E S) {K L : ↥S} (h : Fr.rho K = Fr.rho L)
    (M : ↥S) : (M = K ∨ Commutes (K : Subgroup G) (M : Subgroup G)) ↔
      (M = L ∨ Commutes (L : Subgroup G) (M : Subgroup G)) := by
  rw [← Fr.rho_apply_eq_iff hA2, ← Fr.rho_apply_eq_iff hA2, h]

@[expose] noncomputable def transvection (K : ↥S) : MulAut ↥E :=
  E.normalizerMonoidHom ⟨Fr.w K, Fr.w_mem_normalizer K⟩

theorem transvection_eq (K : ↥S) {w : G} (hw : w ∈ normPart (K : Subgroup G) E)
    (hw' : w ∉ centPart (K : Subgroup G) E) :
    E.normalizerMonoidHom ⟨w, (mem_normPart_iff.mp hw).2⟩ = Fr.transvection K := by
  have hc := (Fr.inSigma K.2).inv_mul_mem_centPart Fr.odd (Fr.w_mem K) (Fr.w_not_mem K) hw hw'
  have hcN : (Fr.w K)⁻¹ * w ∈ Subgroup.normalizer (E : Set G) :=
    (mem_normPart_iff.mp (centPart_le_normPart _ _ hc)).2
  have h2 : (⟨w, (mem_normPart_iff.mp hw).2⟩ : Subgroup.normalizer (E : Set G)) =
      ⟨Fr.w K, Fr.w_mem_normalizer K⟩ * ⟨(Fr.w K)⁻¹ * w, hcN⟩ :=
    Subtype.ext (by simp)
  have h3 : E.normalizerMonoidHom ⟨(Fr.w K)⁻¹ * w, hcN⟩ = 1 := by
    refine MulEquiv.ext fun e => Subtype.ext ?_
    have h4 := (mem_centPart_iff.mp hc).2 e e.2
    show (Fr.w K)⁻¹ * w * e * ((Fr.w K)⁻¹ * w)⁻¹ = e
    rw [← h4]
    group
  rw [h2, map_mul, h3, mul_one]
  rfl

theorem transvection_apply_of_mem_axis (K : ↥S) {e : ↥E} (he : (e : G) ∈ axisSub E (K : Subgroup G)) :
    ((Fr.transvection K e : ↥E) : G) = e :=
  InSigma.conj_eq_of_mem_axis (normPart_le_left _ _ (Fr.w_mem K)) he

theorem transvection_apply_of_not_mem_axis (K : ↥S) {z : G}
    (hz : IsUniqueInvolution (K : Subgroup G) z) {e : ↥E}
    (he : (e : G) ∉ axisSub E (K : Subgroup G)) : ((Fr.transvection K e : ↥E) : G) = e * z :=
  (Fr.inSigma K.2).conj_eq_mul_of_not_mem_axis Fr.odd hz (Fr.w_mem K) (Fr.w_not_mem K) e.2 he

theorem transvection_ne_one (K : ↥S) : Fr.transvection K ≠ 1 := by
  intro h
  obtain ⟨a, haE, ha⟩ := (Fr.inSigma K.2).exists_mem_not_mem_axis
  obtain ⟨z, hz⟩ := Fr.exists_isUniqueInvolution K.2
  have h1 := Fr.transvection_apply_of_not_mem_axis K hz (e := ⟨a, haE⟩) ha
  rw [h] at h1
  have h3 : a = a * z := h1
  exact hz.ne_one (by simpa using h3.symm)

theorem mem_mu_iff (hA2 : A2Dichotomy E S) {π : Equiv.Perm ↥S} :
    π ∈ Fr.mu ↔ ∃ n ∈ weylN E S, Fr.act n = π := by
  have hT := hA2.centTrivial
  constructor
  · intro hπ
    induction hπ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨K, rfl⟩ := hx
      exact ⟨⟨Fr.w K, Fr.w_mem_normalizer K⟩, Subgroup.subset_closure ⟨K, K.2, Fr.w_mem K⟩, rfl⟩
    | one => exact ⟨1, one_mem _, map_one _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      exact ⟨n * m, mul_mem hn hm, map_mul _ _ _⟩
    | inv x _ hx =>
      obtain ⟨n, hn, rfl⟩ := hx
      exact ⟨n⁻¹, inv_mem hn, map_inv _ _⟩
  · rintro ⟨n, hn, rfl⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨K, hK, hxK⟩ := hx
      by_cases hc : (x : G) ∈ centPart K E
      · rw [Fr.act_eq_one_of_forall fun L hL => hT K hK _ hc L hL]
        exact one_mem _
      · have := Fr.act_eq_rho hT (K := ⟨K, hK⟩) hxK hc
        rw [show (⟨(x : G), (mem_normPart_iff.mp hxK).2⟩ : Subgroup.normalizer (E : Set G)) = x
          from rfl] at this
        rw [this]
        exact Fr.rho_mem_mu _
    | one => rw [map_one]; exact one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact inv_mem hx

omit [Finite F] in
theorem commute_of_act_eq_one {n : Subgroup.normalizer (E : Set G)} (h : Fr.act n = 1) {e : G}
    (he : e ∈ E) : (n : G) * e = e * (n : G) := by
  have hle : Subgroup.closure (zSet S) ≤ Subgroup.centralizer ({(n : G)} : Set G) := by
    rw [Subgroup.closure_le]
    rintro z ⟨K, hK, hz⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have h1 := hz.conj_eq (Fr.conjSub_eq_of_act_eq_one h hK)
    calc (n : G) * z = (n : G) * z * (n : G)⁻¹ * (n : G) := by group
      _ = z * (n : G) := by rw [h1]
  have he' : e ∈ Subgroup.closure (zSet S) := by rw [Fr.gen]; exact he
  exact Subgroup.mem_centralizer_iff.mp (hle he') (n : G) rfl

@[expose] noncomputable def NtoMu (hA2 : A2Dichotomy E S) : ↥(weylN E S) →* ↥Fr.mu :=
  (Fr.act.comp (weylN E S).subtype).codRestrict Fr.mu fun n =>
    (Fr.mem_mu_iff hA2).mpr ⟨n, n.2, rfl⟩

theorem NtoMu_surjective (hA2 : A2Dichotomy E S) : Function.Surjective (Fr.NtoMu hA2) := by
  intro π
  obtain ⟨n, hn, h⟩ := (Fr.mem_mu_iff hA2).mp π.2
  exact ⟨⟨n, hn⟩, Subtype.ext h⟩

theorem NtoMu_ker_le (hA2 : A2Dichotomy E S) :
    (Fr.NtoMu hA2).ker ≤ (E.normalizerMonoidHom.comp (weylN E S).subtype).ker := by
  intro n hn
  rw [MonoidHom.mem_ker] at hn ⊢
  have h1 : Fr.act (n : Subgroup.normalizer (E : Set G)) = 1 := congrArg Subtype.val hn
  refine MulEquiv.ext fun e => Subtype.ext ?_
  have h2 := Fr.commute_of_act_eq_one h1 e.2
  show (n : G) * e * (n : G)⁻¹ = e
  rw [h2]
  group

@[expose] noncomputable def muAct (hA2 : A2Dichotomy E S) : ↥Fr.mu →* MulAut ↥E :=
  MonoidHom.liftOfSurjective (Fr.NtoMu hA2) (Fr.NtoMu_surjective hA2)
    ⟨E.normalizerMonoidHom.comp (weylN E S).subtype, Fr.NtoMu_ker_le hA2⟩

theorem muAct_NtoMu (hA2 : A2Dichotomy E S) (n : ↥(weylN E S)) (e : ↥E) :
    ((Fr.muAct hA2 (Fr.NtoMu hA2 n) e : ↥E) : G) = ((n : Subgroup.normalizer (E : Set G)) : G) * e *
      ((n : Subgroup.normalizer (E : Set G)) : G)⁻¹ := by
  simp only [muAct, MonoidHom.liftOfRightInverse_comp_apply]
  rfl

theorem muAct_rhoMu (hA2 : A2Dichotomy E S) (K : ↥S) (e : ↥E) :
    ((Fr.muAct hA2 (Fr.rhoMu K) e : ↥E) : G) = Fr.w K * e * (Fr.w K)⁻¹ := by
  have hK : Fr.rhoMu K = Fr.NtoMu hA2
      ⟨⟨Fr.w K, Fr.w_mem_normalizer K⟩, Subgroup.subset_closure ⟨K, K.2, Fr.w_mem K⟩⟩ := rfl
  rw [hK, muAct_NtoMu]

theorem muAct_rhoMu_eq_transvection (hA2 : A2Dichotomy E S) (K : ↥S) :
    Fr.muAct hA2 (Fr.rhoMu K) = Fr.transvection K := by
  refine MulEquiv.ext fun e => Subtype.ext ?_
  rw [Fr.muAct_rhoMu hA2 K e]
  rfl

theorem muAct_rhoMu_of_mem_axis (hA2 : A2Dichotomy E S) (K : ↥S) {e : ↥E}
    (he : (e : G) ∈ axisSub E (K : Subgroup G)) : ((Fr.muAct hA2 (Fr.rhoMu K) e : ↥E) : G) = e := by
  rw [Fr.muAct_rhoMu hA2 K e]
  exact InSigma.conj_eq_of_mem_axis (normPart_le_left _ _ (Fr.w_mem K)) he

theorem muAct_rhoMu_of_not_mem_axis (hA2 : A2Dichotomy E S) (K : ↥S) {z : G}
    (hz : IsUniqueInvolution (K : Subgroup G) z) {e : ↥E}
    (he : (e : G) ∉ axisSub E (K : Subgroup G)) :
    ((Fr.muAct hA2 (Fr.rhoMu K) e : ↥E) : G) = e * z := by
  rw [Fr.muAct_rhoMu hA2 K e]
  exact (Fr.inSigma K.2).conj_eq_mul_of_not_mem_axis Fr.odd hz (Fr.w_mem K) (Fr.w_not_mem K) e.2 he

@[expose] noncomputable def M0 (hA2 : A2Dichotomy E S) : Subgroup ↥Fr.mu := (Fr.muAct hA2).ker

theorem rhoMu_not_mem_M0 (hA2 : A2Dichotomy E S) (K : ↥S) : Fr.rhoMu K ∉ Fr.M0 hA2 := by
  intro h
  obtain ⟨a, haE, ha⟩ := (Fr.inSigma K.2).exists_mem_not_mem_axis
  obtain ⟨z, hz⟩ := Fr.exists_isUniqueInvolution K.2
  have h1 := Fr.muAct_rhoMu_of_not_mem_axis hA2 K hz (e := ⟨a, haE⟩) ha
  have h2 : Fr.muAct hA2 (Fr.rhoMu K) = 1 := h
  rw [h2] at h1
  have h3 : a = a * z := h1
  exact hz.ne_one (by simpa using h3.symm)

theorem M0_sq (hA2 : A2Dichotomy E S) (hfib : FibreLE2 S) {m : ↥Fr.mu} (hm : m ∈ Fr.M0 hA2) :
    m * m = 1 := by
  obtain ⟨n, hn, hnm⟩ := (Fr.mem_mu_iff hA2).mp m.2
  have hmn : m = Fr.NtoMu hA2 ⟨n, hn⟩ := Subtype.ext hnm.symm
  have hfix : ∀ e : G, e ∈ E → (n : G) * e * (n : G)⁻¹ = e := by
    intro e he
    have h1 : Fr.muAct hA2 m = 1 := hm
    have h2 := Fr.muAct_NtoMu hA2 ⟨n, hn⟩ ⟨e, he⟩
    rw [← hmn, h1] at h2
    exact h2.symm
  have hK : ∀ K : ↥S, Fr.act n (Fr.act n K) = K := by
    intro K
    obtain ⟨z, hz⟩ := Fr.exists_isUniqueInvolution K.2
    have hzE := Fr.mem_of_isUniqueInvolution K.2 hz
    have hz1 : IsUniqueInvolution (Fr.act n K : Subgroup G) z := by
      have := hz.conj (n : G)
      rwa [hfix z hzE] at this
    have hz2 : IsUniqueInvolution (Fr.act n (Fr.act n K) : Subgroup G) z := by
      have := hz1.conj (n : G)
      rwa [hfix z hzE] at this
    rcases hfib z K K.2 _ (Fr.act n K).2 _ (Fr.act n (Fr.act n K)).2 hz hz1 hz2 with h | h | h
    · have h1 : Fr.act n K = K := (Subtype.ext h).symm
      rw [h1, h1]
    · exact (Subtype.ext h).symm
    · have h1 : Fr.act n K = Fr.act n (Fr.act n K) := Subtype.ext h
      have h2 : K = Fr.act n K := (Fr.act n).injective h1
      exact h1.symm.trans h2.symm
  refine Subtype.ext ?_
  show (m : Equiv.Perm ↥S) * m = 1
  rw [← hnm]
  exact Equiv.ext fun K => hK K

theorem M0_mul_comm (hA2 : A2Dichotomy E S) (hfib : FibreLE2 S) {a b : ↥Fr.mu}
    (ha : a ∈ Fr.M0 hA2) (hb : b ∈ Fr.M0 hA2) : a * b = b * a := by
  have hab : a * b * (a * b) = 1 := Fr.M0_sq hA2 hfib ((Fr.M0 hA2).mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (Fr.M0_sq hA2 hfib ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (Fr.M0_sq hA2 hfib hb)
  have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  rw [this, _root_.mul_inv_rev, ha', hb']

end ToralFrame

end CFSG.ClassicalInvolution.Generic
