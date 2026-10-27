module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.GenerationCentralizer
import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2Conj

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (O2Trivial)
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

private noncomputable def sigma_g45ie (G M : Subgroup Ω) (N : Subgroup (MulAut ↥(gomiV M)))
    (hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω))
    (hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)) : Set (MulAut ↥(gomiV G)) :=
  {σ | ∃ (m : Ω) (hm : m ∈ M), ∃ y ∈ autOn M (gomiV M),
    conjAct (gomiV M) ⟨m, hWM hm⟩ ∈ N.map (MulAut.conj y).toMonoidHom ∧
    conjAct (gomiV M) ⟨m, hWM hm⟩ ∉
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) ∧
    conjAct (gomiV G) ⟨m, hVM hm⟩ = σ}

private theorem card_eq_six_of_isSLn_two_one_g45ie {X : Type} [Group X] (h : IsSLn X 2 1) :
    Nat.card X = 6 := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  let : Field K := hKf
  have : Finite K := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two K, hK2]
  norm_num

private theorem card_inf_eq_three_g45ie {W : Type} [Group W] {N O : Subgroup (MulAut W)}
    (hSL : IsSLn ↥N 2 1) (hO : Odd (Nat.card ↥O)) (hne : N ⊓ O ≠ ⊥) :
    Nat.card ↥(N ⊓ O) = 3 := by
  have hN6 : Nat.card ↥N = 6 := card_eq_six_of_isSLn_two_one_g45ie hSL
  have hdvd : Nat.card ↥(N ⊓ O) ∣ 6 := by
    rw [← hN6]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hodd : Odd (Nat.card ↥(N ⊓ O)) :=
    hO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hne1 : Nat.card ↥(N ⊓ O) ≠ 1 := fun h1 =>
    hne (Subgroup.eq_bot_of_card_eq (H := N ⊓ O) h1)
  have hdvd3 : Nat.card ↥(N ⊓ O) ∣ 3 :=
    (Odd.coprime_two_right hodd).dvd_of_dvd_mul_left (by simpa using hdvd)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
  · exact absurd h1 hne1
  · exact h3

private theorem index_two_of_card_six_three_g45ie {K : Type*} [Group K] [Finite K]
    {H : Subgroup K} (hK : Nat.card K = 6) (hH : Nat.card ↥H = 3) : H.index = 2 := by
  rw [Subgroup.index_eq_card_div, hK, hH]

private theorem card_inf_map_conj_g45ie {W : Type*} [Group W] {N O : Subgroup (MulAut W)}
    {y : MulAut W} (hO : O.map (MulAut.conj y).toMonoidHom = O)
    (hH0 : Nat.card ↥(N ⊓ O) = 3) :
    Nat.card ↥(N.map (MulAut.conj y).toMonoidHom ⊓ O) = 3 := by
  rw [← hO, ← Subgroup.map_inf N O (MulAut.conj y).toMonoidHom (MulAut.conj y).injective,
    Subgroup.card_map_of_injective (MulAut.conj y).injective, hH0]

private theorem index_two_inf_map_conj_g45ie {W : Type} [Group W] [Finite W]
    {N O : Subgroup (MulAut W)} {y : MulAut W}
    (hSL : IsSLn ↥(N.map (MulAut.conj y).toMonoidHom) 2 1)
    (hO : O.map (MulAut.conj y).toMonoidHom = O)
    (hH0 : Nat.card ↥(N ⊓ O) = 3) :
    (((N.map (MulAut.conj y).toMonoidHom) ⊓ O).subgroupOf
        (N.map (MulAut.conj y).toMonoidHom)).index = 2 := by
  have hK : Nat.card ↥(N.map (MulAut.conj y).toMonoidHom) = 6 :=
    card_eq_six_of_isSLn_two_one_g45ie hSL
  have hH : Nat.card ↥((N.map (MulAut.conj y).toMonoidHom ⊓ O).subgroupOf
      (N.map (MulAut.conj y).toMonoidHom)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact card_inf_map_conj_g45ie hO hH0
  exact index_two_of_card_six_three_g45ie hK hH

private theorem sq_mem_inf_map_conj_g45ie {W : Type*} [Group W]
    {N O : Subgroup (MulAut W)} {y : MulAut W} {x : MulAut W}
    (hidx : (((N.map (MulAut.conj y).toMonoidHom) ⊓ O).subgroupOf
        (N.map (MulAut.conj y).toMonoidHom)).index = 2)
    (hx : x ∈ N.map (MulAut.conj y).toMonoidHom) : x ^ 2 ∈ O := by
  have hmem : (⟨x, hx⟩ : ↥(N.map (MulAut.conj y).toMonoidHom)) ^ 2 ∈
      ((N.map (MulAut.conj y).toMonoidHom) ⊓ O).subgroupOf
        (N.map (MulAut.conj y).toMonoidHom) :=
    Subgroup.sq_mem_of_index_two hidx ⟨x, hx⟩
  exact (Subgroup.mem_subgroupOf.mp hmem).2

omit [Finite Ω] in
private theorem conjAct_mul_g45ie {M : Subgroup Ω} {U : Subgroup Ω}
    (hU : M ≤ Subgroup.normalizer (U : Set Ω))
    {a b : Ω} (ha : a ∈ M) (hb : b ∈ M) :
    conjAct U ⟨a * b, hU (M.mul_mem ha hb)⟩ =
      conjAct U ⟨a, hU ha⟩ * conjAct U ⟨b, hU hb⟩ := by
  rw [show (⟨a * b, hU (M.mul_mem ha hb)⟩ : Subgroup.normalizer (U : Set Ω)) =
    ⟨a, hU ha⟩ * ⟨b, hU hb⟩ from Subtype.ext rfl, map_mul]

omit [Finite Ω] in
private theorem conjAct_mul_inv_g45ie {M : Subgroup Ω} {U : Subgroup Ω}
    (hU : M ≤ Subgroup.normalizer (U : Set Ω)) {a b : Ω} (ha : a ∈ M) (hb : b ∈ M) :
    conjAct U ⟨a * b⁻¹, hU (M.mul_mem ha (M.inv_mem hb))⟩ =
      conjAct U ⟨a, hU ha⟩ * (conjAct U ⟨b, hU hb⟩)⁻¹ := by
  rw [show (⟨a * b⁻¹, hU (M.mul_mem ha (M.inv_mem hb))⟩ :
      Subgroup.normalizer (U : Set Ω)) = ⟨a, hU ha⟩ * (⟨b, hU hb⟩)⁻¹ from
    Subtype.ext (by simp), map_mul, map_inv]

omit [Finite Ω] in
private theorem conjAct_conj_g45ie {M : Subgroup Ω} {U : Subgroup Ω}
    (hU : M ≤ Subgroup.normalizer (U : Set Ω))
    {a b : Ω} (ha : a ∈ M) (hb : b ∈ M) :
    conjAct U ⟨a * b * a⁻¹, hU (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha))⟩ =
      conjAct U ⟨a, hU ha⟩ * conjAct U ⟨b, hU hb⟩ * (conjAct U ⟨a, hU ha⟩)⁻¹ := by
  rw [show (⟨a * b * a⁻¹, hU (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha))⟩ :
      Subgroup.normalizer (U : Set Ω)) = ⟨a, hU ha⟩ * ⟨b, hU hb⟩ * (⟨a, hU ha⟩)⁻¹ from
    Subtype.ext (by simp [mul_assoc]), map_mul, map_mul, map_inv]

private theorem sigma_sq_g45ie {M : Subgroup Ω} {N : Subgroup (MulAut ↥(gomiV M))}
    {hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω)}
    {hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    {m : Ω} {y : MulAut ↥(gomiV M)} (hy : y ∈ autOn M (gomiV M))
    (hD : M ⊓ Subgroup.centralizer (gomiV M : Set Ω) ≤
      Subgroup.centralizer (gomiV G : Set Ω))
    (hH0 : Nat.card ↥(N ⊓ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω))
      (gomiV M)) = 3)
    (hOY : autOn M (gomiV M) ≤ Subgroup.normalizer
      (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) :
        Set (MulAut ↥(gomiV M))))
    (hSL : ∀ K ∈ gomiNSet (autOn M (gomiV M)), IsSLn ↥K 2 1)
    (hN : N ∈ gomiNSet (autOn M (gomiV M)))
    (hm : m ∈ M)
    (hmem : conjAct (gomiV M) ⟨m, hWM hm⟩ ∈ N.map (MulAut.conj y).toMonoidHom) :
    (conjAct (gomiV G) ⟨m, hVM hm⟩) ^ 2 = 1 := by
  have hKy : N.map (MulAut.conj y).toMonoidHom ∈ gomiNSet (autOn M (gomiV M)) :=
    map_conj_mem_gomiNSet hN hy
  have hOmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hOY hy)
  have hidx := index_two_inf_map_conj_g45ie (hSL _ hKy) hOmap hH0
  have hsq : (conjAct (gomiV M) ⟨m, hWM hm⟩) ^ 2 ∈
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) :=
    sq_mem_inf_map_conj_g45ie hidx hmem
  have hsq' : conjAct (gomiV M) ⟨m * m, hWM (M.mul_mem hm hm)⟩ ∈
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) := by
    rw [show (⟨m * m, hWM (M.mul_mem hm hm)⟩ :
        Subgroup.normalizer (gomiV M : Set Ω)) = ⟨m, hWM hm⟩ * ⟨m, hWM hm⟩ from
      Subtype.ext (by simp), map_mul]
    simpa [pow_two] using hsq
  have hm2C : m * m ∈ Subgroup.centralizer (gomiV G : Set Ω) :=
    (AutOn.mem_of_conjAct_mem_autOn hWM inf_le_left (le_inf inf_le_left hD)
      (M.mul_mem hm hm) hsq').2
  have h1 : conjAct (gomiV G) ⟨m * m, hVM (M.mul_mem hm hm)⟩ = 1 :=
    (AutOn.conjAct_eq_one_iff ⟨m * m, hVM (M.mul_mem hm hm)⟩).mpr hm2C
  rw [conjAct_mul_g45ie (U := gomiV G) hVM hm hm] at h1
  rw [pow_two]
  exact h1

private theorem mul_inv_mem_inf_of_index_two_g45ie {X : Type} [Group X]
    {K O : Subgroup X} {a b : X} (hidx : ((K ⊓ O).subgroupOf K).index = 2)
    (ha : a ∈ K) (hb : b ∈ K) (haO : a ∉ O) (hbO : b ∉ O) : a * b⁻¹ ∈ O := by
  have hmem : (⟨a, ha⟩ : ↥K) * (⟨b, hb⟩ : ↥K)⁻¹ ∈ (K ⊓ O).subgroupOf K := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    constructor
    · intro h
      exact absurd (Subgroup.mem_subgroupOf.mp h).2 haO
    · intro h
      exact absurd ((Subgroup.inv_mem_iff O).mp
        (Subgroup.mem_subgroupOf.mp h).2) hbO
  have h' : a * b⁻¹ ∈ K ⊓ O := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using Subgroup.mem_subgroupOf.mp hmem
  exact (Subgroup.mem_inf.mp h').2

omit [Finite Ω] in
private theorem conjAct_eq_of_conjAct_mul_inv_mem_g45ie {M : Subgroup Ω}
    {hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω)}
    {hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    (hD : M ⊓ Subgroup.centralizer (gomiV M : Set Ω) ≤
      Subgroup.centralizer (gomiV G : Set Ω))
    {m₁ m₂ : Ω} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (hO : conjAct (gomiV M) ⟨m₁ * m₂⁻¹, hWM (M.mul_mem hm₁ (M.inv_mem hm₂))⟩ ∈
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M)) :
    conjAct (gomiV G) ⟨m₁, hVM hm₁⟩ = conjAct (gomiV G) ⟨m₂, hVM hm₂⟩ := by
  have hmC : m₁ * m₂⁻¹ ∈ Subgroup.centralizer (gomiV G : Set Ω) :=
    (AutOn.mem_of_conjAct_mem_autOn hWM inf_le_left (le_inf inf_le_left hD)
      (M.mul_mem hm₁ (M.inv_mem hm₂)) hO).2
  have h1 : conjAct (gomiV G) ⟨m₁ * m₂⁻¹, hVM (M.mul_mem hm₁ (M.inv_mem hm₂))⟩ = 1 :=
    (AutOn.conjAct_eq_one_iff _).mpr hmC
  rw [conjAct_mul_inv_g45ie (U := gomiV G) hVM hm₁ hm₂, mul_inv_eq_one] at h1
  exact h1

private theorem sigma_comm_eq_conj_g45ie {M : Subgroup Ω} {N : Subgroup (MulAut ↥(gomiV M))}
    {hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω)}
    {hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    (hD : M ⊓ Subgroup.centralizer (gomiV M : Set Ω) ≤
      Subgroup.centralizer (gomiV G : Set Ω))
    (hH0 : Nat.card ↥(N ⊓ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω))
      (gomiV M)) = 3)
    (hOY : autOn M (gomiV M) ≤ Subgroup.normalizer
      (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) :
        Set (MulAut ↥(gomiV M))))
    (hSL : ∀ K ∈ gomiNSet (autOn M (gomiV M)), IsSLn ↥K 2 1)
    (hN : N ∈ gomiNSet (autOn M (gomiV M)))
    {m₁ m₂ : Ω} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    {y₁ y₂ : MulAut ↥(gomiV M)} (hy₁ : y₁ ∈ autOn M (gomiV M))
    (hmem₁ : conjAct (gomiV M) ⟨m₁, hWM hm₁⟩ ∈ N.map (MulAut.conj y₁).toMonoidHom)
    (hnot₁ : conjAct (gomiV M) ⟨m₁, hWM hm₁⟩ ∉
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M))
    (hmem₂ : conjAct (gomiV M) ⟨m₂, hWM hm₂⟩ ∈ N.map (MulAut.conj y₂).toMonoidHom)
    (hnot₂ : conjAct (gomiV M) ⟨m₂, hWM hm₂⟩ ∉
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M))
    (hK : N.map (MulAut.conj y₁).toMonoidHom = N.map (MulAut.conj y₂).toMonoidHom) :
    conjAct (gomiV G) ⟨m₁, hVM hm₁⟩ * conjAct (gomiV G) ⟨m₂, hVM hm₂⟩ =
      conjAct (gomiV G) ⟨m₂, hVM hm₂⟩ * conjAct (gomiV G) ⟨m₁, hVM hm₁⟩ := by
  have hmem₂' : conjAct (gomiV M) ⟨m₂, hWM hm₂⟩ ∈
      N.map (MulAut.conj y₁).toMonoidHom := by
    rwa [hK]
  have hOmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hOY hy₁)
  have hidx := index_two_inf_map_conj_g45ie (hSL _ (map_conj_mem_gomiNSet hN hy₁)) hOmap hH0
  have hO : conjAct (gomiV M) ⟨m₁ * m₂⁻¹, hWM (M.mul_mem hm₁ (M.inv_mem hm₂))⟩ ∈
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) := by
    rw [conjAct_mul_inv_g45ie (U := gomiV M) hWM hm₁ hm₂]
    exact mul_inv_mem_inf_of_index_two_g45ie hidx hmem₁ hmem₂' hnot₁ hnot₂
  rw [conjAct_eq_of_conjAct_mul_inv_mem_g45ie hD hm₁ hm₂ hO]

omit [Finite Ω] in
private theorem sigma_comm_ne_conj_g45ie {M : Subgroup Ω} {N : Subgroup (MulAut ↥(gomiV M))}
    {hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω)}
    {hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    (hD : M ⊓ Subgroup.centralizer (gomiV M : Set Ω) ≤
      Subgroup.centralizer (gomiV G : Set Ω))
    (hPair : (gomiNSet (autOn M (gomiV M))).Pairwise
      (fun K K' => ∀ x ∈ K, ∀ y ∈ K', x * y = y * x))
    (hN : N ∈ gomiNSet (autOn M (gomiV M)))
    {m₁ m₂ : Ω} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    {y₁ y₂ : MulAut ↥(gomiV M)} (hy₁ : y₁ ∈ autOn M (gomiV M))
    (hy₂ : y₂ ∈ autOn M (gomiV M))
    (hmem₁ : conjAct (gomiV M) ⟨m₁, hWM hm₁⟩ ∈ N.map (MulAut.conj y₁).toMonoidHom)
    (hmem₂ : conjAct (gomiV M) ⟨m₂, hWM hm₂⟩ ∈ N.map (MulAut.conj y₂).toMonoidHom)
    (hK : N.map (MulAut.conj y₁).toMonoidHom ≠ N.map (MulAut.conj y₂).toMonoidHom) :
    conjAct (gomiV G) ⟨m₁, hVM hm₁⟩ * conjAct (gomiV G) ⟨m₂, hVM hm₂⟩ =
      conjAct (gomiV G) ⟨m₂, hVM hm₂⟩ * conjAct (gomiV G) ⟨m₁, hVM hm₁⟩ := by
  have hcommW : conjAct (gomiV M) ⟨m₁, hWM hm₁⟩ * conjAct (gomiV M) ⟨m₂, hWM hm₂⟩ =
      conjAct (gomiV M) ⟨m₂, hWM hm₂⟩ * conjAct (gomiV M) ⟨m₁, hWM hm₁⟩ :=
    hPair (map_conj_mem_gomiNSet hN hy₁) (map_conj_mem_gomiNSet hN hy₂) hK _ hmem₁ _ hmem₂
  have heqW : conjAct (gomiV M) ⟨m₁ * m₂, hWM (M.mul_mem hm₁ hm₂)⟩ =
      conjAct (gomiV M) ⟨m₂ * m₁, hWM (M.mul_mem hm₂ hm₁)⟩ := by
    rw [conjAct_mul_g45ie hWM hm₁ hm₂, conjAct_mul_g45ie hWM hm₂ hm₁]
    exact hcommW
  have hW1 : conjAct (gomiV M) ⟨(m₁ * m₂) * (m₂ * m₁)⁻¹,
      hWM (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem (M.mul_mem hm₂ hm₁)))⟩ = 1 := by
    rw [conjAct_mul_inv_g45ie hWM (M.mul_mem hm₁ hm₂) (M.mul_mem hm₂ hm₁), heqW,
      mul_inv_cancel]
  have hmD : (m₁ * m₂) * (m₂ * m₁)⁻¹ ∈
      M ⊓ Subgroup.centralizer (gomiV M : Set Ω) :=
    ⟨M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem (M.mul_mem hm₂ hm₁)),
      (AutOn.conjAct_eq_one_iff _).mp hW1⟩
  have h1 : conjAct (gomiV G) ⟨(m₁ * m₂) * (m₂ * m₁)⁻¹,
      hVM (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem (M.mul_mem hm₂ hm₁)))⟩ = 1 :=
    (AutOn.conjAct_eq_one_iff _).mpr (hD hmD)
  rw [conjAct_mul_inv_g45ie hVM (M.mul_mem hm₁ hm₂) (M.mul_mem hm₂ hm₁),
    conjAct_mul_g45ie hVM hm₁ hm₂, conjAct_mul_g45ie hVM hm₂ hm₁,
    mul_inv_eq_one] at h1
  exact h1

private theorem sigma_comm_g45ie {M : Subgroup Ω} {N : Subgroup (MulAut ↥(gomiV M))}
    {hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω)}
    {hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    (hD : M ⊓ Subgroup.centralizer (gomiV M : Set Ω) ≤
      Subgroup.centralizer (gomiV G : Set Ω))
    (hH0 : Nat.card ↥(N ⊓ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω))
      (gomiV M)) = 3)
    (hOY : autOn M (gomiV M) ≤ Subgroup.normalizer
      (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) :
        Set (MulAut ↥(gomiV M))))
    (hSL : ∀ K ∈ gomiNSet (autOn M (gomiV M)), IsSLn ↥K 2 1)
    (hPair : (gomiNSet (autOn M (gomiV M))).Pairwise
      (fun K K' => ∀ x ∈ K, ∀ y ∈ K', x * y = y * x))
    (hN : N ∈ gomiNSet (autOn M (gomiV M)))
    {m₁ m₂ : Ω} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    {y₁ y₂ : MulAut ↥(gomiV M)} (hy₁ : y₁ ∈ autOn M (gomiV M))
    (hy₂ : y₂ ∈ autOn M (gomiV M))
    (hmem₁ : conjAct (gomiV M) ⟨m₁, hWM hm₁⟩ ∈ N.map (MulAut.conj y₁).toMonoidHom)
    (hnot₁ : conjAct (gomiV M) ⟨m₁, hWM hm₁⟩ ∉
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M))
    (hmem₂ : conjAct (gomiV M) ⟨m₂, hWM hm₂⟩ ∈ N.map (MulAut.conj y₂).toMonoidHom)
    (hnot₂ : conjAct (gomiV M) ⟨m₂, hWM hm₂⟩ ∉
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M)) :
    conjAct (gomiV G) ⟨m₁, hVM hm₁⟩ * conjAct (gomiV G) ⟨m₂, hVM hm₂⟩ =
      conjAct (gomiV G) ⟨m₂, hVM hm₂⟩ * conjAct (gomiV G) ⟨m₁, hVM hm₁⟩ := by
  by_cases hK : N.map (MulAut.conj y₁).toMonoidHom = N.map (MulAut.conj y₂).toMonoidHom
  · exact sigma_comm_eq_conj_g45ie hD hH0 hOY hSL hN hm₁ hm₂ hy₁ hmem₁ hnot₁ hmem₂ hnot₂ hK
  · exact sigma_comm_ne_conj_g45ie hD hPair hN hm₁ hm₂ hy₁ hy₂ hmem₁ hmem₂ hK

omit [Finite Ω] in
private theorem sigma_conj_g45ie {M : Subgroup Ω} {N : Subgroup (MulAut ↥(gomiV M))}
    {hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω)}
    {hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    (hOY : autOn M (gomiV M) ≤ Subgroup.normalizer
      (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) :
        Set (MulAut ↥(gomiV M))))
    {m' : Ω} (hm' : m' ∈ M)
    {m : Ω} (hm : m ∈ M) {y : MulAut ↥(gomiV M)} (hy : y ∈ autOn M (gomiV M))
    (hmem : conjAct (gomiV M) ⟨m, hWM hm⟩ ∈ N.map (MulAut.conj y).toMonoidHom)
    (hnot : conjAct (gomiV M) ⟨m, hWM hm⟩ ∉
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M)) :
    conjAct (gomiV G) ⟨m', hVM hm'⟩ * conjAct (gomiV G) ⟨m, hVM hm⟩ *
        (conjAct (gomiV G) ⟨m', hVM hm'⟩)⁻¹ ∈ sigma_g45ie G M N hWM hVM := by
  let y' : MulAut ↥(gomiV M) := conjAct (gomiV M) ⟨m', hWM hm'⟩
  have hy' : y' ∈ autOn M (gomiV M) := AutOn.conjAct_mem_autOn_of_mem (hWM hm') hm'
  have hm'' : m' * m * m'⁻¹ ∈ M := M.mul_mem (M.mul_mem hm' hm) (M.inv_mem hm')
  have hz := conjAct_conj_g45ie hWM hm' hm
  have hOz : (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M)).map
      (MulAut.conj y'⁻¹).toMonoidHom =
      autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hOY ((autOn M (gomiV M)).inv_mem hy'))
  refine ⟨m' * m * m'⁻¹, hm'', y' * y, (autOn M (gomiV M)).mul_mem hy' hy, ?_, ?_, ?_⟩
  · obtain ⟨n, hn, hne⟩ := hmem
    refine Subgroup.mem_map.mpr ⟨n, hn, ?_⟩
    have hconj : (MulAut.conj (y' * y)).toMonoidHom n =
        y' * (MulAut.conj y).toMonoidHom n * y'⁻¹ := by
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MulAut.conj_apply]
      group
    rw [hconj, hne]
    exact hz.symm
  · intro hmemO
    have hmemO' : y' * conjAct (gomiV M) ⟨m, hWM hm⟩ * y'⁻¹ ∈
        autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) := by
      rwa [hz] at hmemO
    apply hnot
    have hmap : (MulAut.conj y'⁻¹).toMonoidHom
        (y' * conjAct (gomiV M) ⟨m, hWM hm⟩ * y'⁻¹) ∈
        (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M)).map
          (MulAut.conj y'⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨_, hmemO', rfl⟩
    rw [hOz] at hmap
    rwa [show (MulAut.conj y'⁻¹).toMonoidHom
        (y' * conjAct (gomiV M) ⟨m, hWM hm⟩ * y'⁻¹) =
        conjAct (gomiV M) ⟨m, hWM hm⟩ from by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group] at hmap
  · exact conjAct_conj_g45ie hVM hm' hm

private theorem sigma_nonempty_g45ie {M : Subgroup Ω} {N : Subgroup (MulAut ↥(gomiV M))}
    {hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω)}
    {hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    (hH0 : Nat.card ↥(N ⊓ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω))
      (gomiV M)) = 3)
    (hSL : IsSLn ↥N 2 1) (hN : N ∈ gomiNSet (autOn M (gomiV M))) :
    (sigma_g45ie G M N hWM hVM).Nonempty := by
  have hN6 : Nat.card ↥N = 6 := card_eq_six_of_isSLn_two_one_g45ie hSL
  have hnotle : ¬ N ≤ N ⊓ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) := by
    intro hle
    have hle' : Nat.card ↥N ≤ Nat.card ↥(N ⊓
        autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M)) :=
      Subgroup.card_le_of_le hle
    omega
  obtain ⟨x, hxN, hxO⟩ := Set.not_subset.mp hnotle
  have hxY : x ∈ autOn M (gomiV M) := le_of_mem_gomiNSet hN hxN
  obtain ⟨n, hn, hne⟩ := AutOn.mem_autOn_iff.mp hxY
  have hwm : conjAct (gomiV M) ⟨(n : Ω), hWM hn⟩ = x := by
    rw [show (⟨(n : Ω), hWM hn⟩ : Subgroup.normalizer (gomiV M : Set Ω)) = n from
      Subtype.ext rfl]
    exact hne
  refine ⟨conjAct (gomiV G) ⟨(n : Ω), hVM hn⟩, ⟨(n : Ω), hn, 1,
    (autOn M (gomiV M)).one_mem, ?_, ?_, rfl⟩⟩
  · simpa [hwm] using hxN
  · rw [hwm]
    exact fun hxO' => hxO ⟨hxN, hxO'⟩

omit [Finite Ω] in
private theorem sigma_inv_g45ie {M : Subgroup Ω} {N : Subgroup (MulAut ↥(gomiV M))}
    {hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω)}
    {hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    (hOY : autOn M (gomiV M) ≤ Subgroup.normalizer
      (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) :
        Set (MulAut ↥(gomiV M))))
    {τ : MulAut ↥(gomiV G)} (hτ : τ ∈ autOn M (gomiV G))
    {σ : MulAut ↥(gomiV G)} (hσ : σ ∈ sigma_g45ie G M N hWM hVM) :
    τ * σ * τ⁻¹ ∈ sigma_g45ie G M N hWM hVM := by
  obtain ⟨m, hm, y, hy, hmem, hnot, hσ'⟩ := hσ
  obtain ⟨n, hn, hτn⟩ := AutOn.mem_autOn_iff.mp hτ
  have hτ' : conjAct (gomiV G) ⟨(n : Ω), hVM hn⟩ = τ := by
    rw [show (⟨(n : Ω), hVM hn⟩ : Subgroup.normalizer (gomiV G : Set Ω)) = n from
      Subtype.ext rfl]
    exact hτn
  rw [← hσ', ← hτ']
  exact sigma_conj_g45ie hOY hn hm hy hmem hnot

omit [Finite Ω] in
private theorem one_not_mem_sigma_g45ie {M : Subgroup Ω} {N : Subgroup (MulAut ↥(gomiV M))}
    {hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω)}
    {hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)} :
    (1 : MulAut ↥(gomiV G)) ∉ sigma_g45ie G M N hWM hVM := by
  rintro ⟨m, hm, y, -, -, hnot, h1⟩
  exact hnot (AutOn.conjAct_mem_autOn_of_mem (hWM hm)
    ⟨hm, (AutOn.conjAct_eq_one_iff ⟨m, hVM hm⟩).mp h1⟩)

private theorem sigma_exists_ne_one_g45ie {M : Subgroup Ω} {N : Subgroup (MulAut ↥(gomiV M))}
    {hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω)}
    {hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω)}
    (hH0 : Nat.card ↥(N ⊓ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω))
      (gomiV M)) = 3)
    (hSL : IsSLn ↥N 2 1) (hN : N ∈ gomiNSet (autOn M (gomiV M))) :
    ∃ σ ∈ sigma_g45ie G M N hWM hVM, σ ≠ 1 := by
  obtain ⟨σ, hσ⟩ := sigma_nonempty_g45ie hH0 hSL hN
  exact ⟨σ, hσ, fun h1 => one_not_mem_sigma_g45ie (M := M) (N := N)
    (hWM := hWM) (hVM := hVM) (h1 ▸ hσ)⟩

private theorem closure_subgroupOf_normal_g45ie {X : Type*} [Group X]
    {A : Subgroup (MulAut X)} {Sigma : Set (MulAut X)} (hSigmaA : Sigma ⊆ A)
    (hinv : ∀ τ ∈ A, ∀ σ ∈ Sigma, τ * σ * τ⁻¹ ∈ Sigma) :
    ((Subgroup.closure Sigma).subgroupOf A).Normal := by
  have hle : Subgroup.closure Sigma ≤ A := (Subgroup.closure_le A).mpr hSigmaA
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro τ hτ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have himage : (⇑(MulAut.conj τ)) '' Sigma = Sigma := by
    apply Set.Subset.antisymm
    · rintro _ ⟨σ, hσ, rfl⟩
      simpa [MulAut.conj_apply] using hinv τ hτ σ hσ
    · intro σ hσ
      refine ⟨τ⁻¹ * σ * τ, ?_, ?_⟩
      · simpa [mul_assoc] using hinv τ⁻¹ (A.inv_mem hτ) σ hσ
      · simp [MulAut.conj_apply, mul_assoc]
  rw [MonoidHom.map_closure]
  change Subgroup.closure ((⇑(MulAut.conj τ)) '' Sigma) = Subgroup.closure Sigma
  rw [himage]

private theorem exists_nontrivial_normal_isPGroup_two_g45ie {X : Type*} [Group X]
    {A : Subgroup (MulAut X)} {Sigma : Set (MulAut X)}
    (hSigmaA : Sigma ⊆ A) (hsq : ∀ σ ∈ Sigma, σ ^ 2 = 1)
    (hcomm : ∀ σ₁ ∈ Sigma, ∀ σ₂ ∈ Sigma, σ₁ * σ₂ = σ₂ * σ₁)
    (hinv : ∀ τ ∈ A, ∀ σ ∈ Sigma, τ * σ * τ⁻¹ ∈ Sigma)
    (hne : ∃ σ ∈ Sigma, σ ≠ 1) :
    ∃ P : Subgroup (MulAut X), P ≤ A ∧ (P.subgroupOf A).Normal ∧ IsPGroup 2 P ∧ P ≠ ⊥ := by
  have hpair : Sigma.Pairwise Commute :=
    fun σ₁ h₁ σ₂ h₂ _ => (commute_iff_eq σ₁ σ₂).mpr (hcomm σ₁ h₁ σ₂ h₂)
  let P : Subgroup (MulAut X) := Subgroup.closure Sigma
  have hPle : P ≤ A := (Subgroup.closure_le A).mpr hSigmaA
  have hPcomm : IsMulCommutative ↥P := Subgroup.isMulCommutative_closure hpair
  have hPsq : ∀ x ∈ P, x ^ 2 = 1 := by
    intro x hx
    change x ∈ Subgroup.closure Sigma at hx
    induction hx using Subgroup.closure_induction with
    | mem σ hσ => exact hsq σ hσ
    | one => simp
    | mul a b ha hb iha ihb =>
        have hcab : a * b = b * a := by
          simpa using congrArg Subtype.val (hPcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        calc (a * b) ^ 2 = a * b * (a * b) := by rw [pow_two]
          _ = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hcab]
          _ = a * a * (b * b) := by group
          _ = 1 := by rw [← pow_two, ← pow_two, iha, ihb, mul_one]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hP2 : IsPGroup 2 ↥P := fun x => ⟨1, by
    have h : ((x : ↥P) : MulAut X) ^ 2 = 1 := hPsq x x.2
    simpa using Subtype.ext h⟩
  have hPnormal : (P.subgroupOf A).Normal := closure_subgroupOf_normal_g45ie hSigmaA hinv
  have hPne : P ≠ ⊥ := by
    obtain ⟨σ, hσ, hσ1⟩ := hne
    have hσP : σ ∈ P := Subgroup.subset_closure hσ
    intro hbot
    rw [hbot] at hσP
    exact hσ1 (by simpa using hσP)
  exact ⟨P, hPle, hPnormal, hP2, hPne⟩

private theorem sigma_facts_g45ie (h : GomiThm45Counterexample c G S) (h31 : GomiFact31)
    {M : Subgroup Ω} (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    {N : Subgroup (MulAut ↥(gomiV M))} (hN : N ∈ gomiNSet (autOn M (gomiV M)))
    (hne : N ⊓ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) ≠ ⊥) :
    ∃ Sigma : Set (MulAut ↥(gomiV G)),
      Sigma ⊆ autOn M (gomiV G) ∧ (∀ σ ∈ Sigma, σ ^ 2 = 1) ∧
      (∀ σ₁ ∈ Sigma, ∀ σ₂ ∈ Sigma, σ₁ * σ₂ = σ₂ * σ₁) ∧
      (∀ τ ∈ autOn M (gomiV G), ∀ σ ∈ Sigma, τ * σ * τ⁻¹ ∈ Sigma) ∧
      (∃ σ ∈ Sigma, σ ≠ 1) := by
  have hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω) := (gomiV_moduleSetting M).2
  have hVM : M ≤ Subgroup.normalizer (gomiV G : Set Ω) := hMG.trans (gomiV_moduleSetting G).2
  have hD : M ⊓ Subgroup.centralizer (gomiV M : Set Ω) ≤
      Subgroup.centralizer (gomiV G : Set Ω) := inf_centralizer_gomiV_le h hMG hGM
  have hOodd : Odd (Nat.card (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω))
      (gomiV M))) := odd_card_autOn_inf_centralizer h hMG hGM
  have h0 : (gomiPstar0Set (autOn M (gomiV M))).Nonempty := by
    obtain ⟨A, hA, rfl⟩ := hN
    exact ⟨A, hA⟩
  have hG0 : O2Trivial (gomiGstar0 (autOn M (gomiV M))) :=
    o2Trivial_of_normal (o2Trivial_autOn_gomiV h hMG hGM)
      (gomiGstar0_le _) (gomiGstar0_subgroupOf_normal _)
  have hW2 : ∀ w : ↥(gomiV M), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (gomiV_moduleSetting M).1.2 w w.2)
  obtain ⟨⟨hSL, -, hPair, -⟩, -⟩ :=
    h31 ↥(gomiV M) hW2 (autOn M (gomiV M)) h0 hG0
  have hH0 : Nat.card ↥(N ⊓ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω))
      (gomiV M)) = 3 := card_inf_eq_three_g45ie (hSL N hN) hOodd hne
  have hOY := le_normalizer_autOn_inf_centralizer hMG (gomiV_moduleSetting G).2
  refine ⟨sigma_g45ie G M N hWM hVM, ?_, ?_, ?_, ?_, ?_⟩
  · rintro σ ⟨m, hm, y, -, -, -, rfl⟩
    exact AutOn.conjAct_mem_autOn_of_mem (hVM hm) hm
  · rintro σ ⟨m, hm, y, hy, hmem, -, rfl⟩
    exact sigma_sq_g45ie (M := M) (N := N) (hWM := hWM) (hVM := hVM) hy hD hH0 hOY hSL hN hm hmem
  · rintro σ₁ ⟨m₁, hm₁, y₁, hy₁, hmem₁, hnot₁, rfl⟩
    rintro σ₂ ⟨m₂, hm₂, y₂, hy₂, hmem₂, hnot₂, rfl⟩
    exact sigma_comm_g45ie hD hH0 hOY hSL hPair hN hm₁ hm₂ hy₁ hy₂ hmem₁ hnot₁ hmem₂ hnot₂
  · intro τ hτ σ hσ
    exact sigma_inv_g45ie (M := M) (N := N) (hWM := hWM) (hVM := hVM) hOY hτ hσ
  · exact sigma_exists_ne_one_g45ie (M := M) (N := N) (hWM := hWM) (hVM := hVM)
      hH0 (hSL N hN) hN

private theorem false_of_sigma_data_g45ie (h : GomiThm45Counterexample c G S)
    {M : Subgroup Ω} (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    {Sigma : Set (MulAut ↥(gomiV G))} (hSigmaA : Sigma ⊆ autOn M (gomiV G))
    (hSigmaSq : ∀ σ ∈ Sigma, σ ^ 2 = 1)
    (hSigmaComm : ∀ σ₁ ∈ Sigma, ∀ σ₂ ∈ Sigma, σ₁ * σ₂ = σ₂ * σ₁)
    (hSigmaInv : ∀ τ ∈ autOn M (gomiV G), ∀ σ ∈ Sigma, τ * σ * τ⁻¹ ∈ Sigma)
    (hSigmaNe : ∃ σ ∈ Sigma, σ ≠ 1) : False := by
  obtain ⟨P, hPle, hPnorm, hP2, hPne⟩ :=
    exists_nontrivial_normal_isPGroup_two_g45ie hSigmaA hSigmaSq hSigmaComm hSigmaInv hSigmaNe
  have hO2M : O2Trivial (autOn M (gomiV G)) :=
    o2Trivial_of_normal (o2Trivial_autOn h) (AutOn.autOn_mono hMG)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (AutOn.autOn_mono hMG)).mpr
        (AutOn.autOn_le_normalizer_autOn hGM))
  exact hPne (hO2M P hPle hPnorm hP2)

theorem inf_autOn_inf_centralizer_eq_bot (h : GomiThm45Counterexample c G S)
    (h31 : GomiFact31) {M : Subgroup Ω} (hMG : M ≤ G)
    (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) {N : Subgroup (MulAut ↥(gomiV M))}
    (hN : N ∈ gomiNSet (autOn M (gomiV M))) :
    N ⊓ autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) = ⊥ := by
  by_contra hne
  obtain ⟨Sigma, hA, hSq, hComm, hInv, hNe⟩ := sigma_facts_g45ie h h31 hMG hGM hN hne
  exact false_of_sigma_data_g45ie h hMG hGM hA hSq hComm hInv hNe

end CFSG.GroupTheory.GomiThm45Counterexample
