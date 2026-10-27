module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI3a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI1b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma dI3b_inf_zpowers_eq_bot {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1)
    {P : Subgroup G} (hxP : x ∉ P) : Subgroup.zpowers x ⊓ P = ⊥ := by
  have hcardx : Nat.card ↥(Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rwa [pow_two]) hx1
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  by_contra hy1
  have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ P) ∣ 2 := by
    rw [← hcardx]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Subgroup.zpowers x ⊓ P ≠ ⊥ := by
    intro hbot
    rw [hbot] at hy
    exact hy1 (Subgroup.mem_bot.mp hy)
  have hne1 : Nat.card ↥(Subgroup.zpowers x ⊓ P) ≠ 1 := by
    intro h1
    exact hne (Subgroup.eq_bot_of_card_eq (Subgroup.zpowers x ⊓ P) h1)
  have hcard2 : Nat.card ↥(Subgroup.zpowers x ⊓ P) = 2 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exact absurd h1 hne1
    · exact h2
  have hle : Subgroup.zpowers x ≤ P := by
    have heq : Subgroup.zpowers x ⊓ P = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard2, hcardx])
    exact heq ▸ inf_le_right
  exact hxP (hle (Subgroup.mem_zpowers x))

private theorem dI3b_comm (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G))
    (hlo : lam * om * lam⁻¹ = om) {j : G} (hj : j ∈ lam • ((q13A t tau x₁ x₂ rho
      ⊔ closure ({tau, om} : Set G) : Subgroup G) : Set G)) :
    j * tau = tau * j ∧ j * om = om * j ∧ j * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * j ∧
      j ∉ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) := by
  obtain ⟨p, hp, hpj⟩ := Set.mem_smul_set.mp hj
  rw [smul_eq_mul] at hpj
  have hK_le_CO : closure ({tau, om} : Set G) ≤ closure ({t, om} : Set G) := by
    rw [← hI]; exact inf_le_left
  have htau_mem : tau ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hom_mem : om ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hzA : (x₁ * x₂) ^ 2 ∈ q13A t tau x₁ x₂ rho :=
    q13a_V_le_A h (Subgroup.subset_closure (by simp))
  have hz_mem : (x₁ * x₂) ^ 2 ∈
      (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) : Subgroup G) :=
    Subgroup.mem_sup_left hzA
  have hP1c := q13d_I_P1_comm h hI
  have hptau : p * tau = tau * p := hP1c p hp tau htau_mem
  have hpom : p * om = om * p := hP1c p hp om hom_mem
  have hpz : p * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * p := hP1c p hp _ hz_mem
  have hltau : lam * tau = tau * lam := q13c_lam_cent_tau h
  have hlom : lam * om = om * lam := by
    calc lam * om = lam * om * lam⁻¹ * lam := by group
      _ = om * lam := by rw [hlo]
  have hlz : lam * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * lam := q13c_lam_z h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hpj]
    calc (lam * p) * tau = lam * (p * tau) := by group
      _ = lam * (tau * p) := by rw [hptau]
      _ = (lam * tau) * p := by group
      _ = (tau * lam) * p := by rw [hltau]
      _ = tau * (lam * p) := by group
  · rw [← hpj]
    calc (lam * p) * om = lam * (p * om) := by group
      _ = lam * (om * p) := by rw [hpom]
      _ = (lam * om) * p := by group
      _ = (om * lam) * p := by rw [hlom]
      _ = om * (lam * p) := by group
  · rw [← hpj]
    calc (lam * p) * (x₁ * x₂) ^ 2 = lam * (p * (x₁ * x₂) ^ 2) := by group
      _ = lam * ((x₁ * x₂) ^ 2 * p) := by rw [hpz]
      _ = (lam * (x₁ * x₂) ^ 2) * p := by group
      _ = ((x₁ * x₂) ^ 2 * lam) * p := by rw [hlz]
      _ = (x₁ * x₂) ^ 2 * (lam * p) := by group
  · intro hjP1
    have hlamP1 : lam ∈
        (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) : Subgroup G) := by
      have hp_inv : p⁻¹ ∈
          (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) : Subgroup G) :=
        Subgroup.inv_mem _ hp
      have hlam_eq : lam = j * p⁻¹ := by rw [← hpj]; group
      rw [hlam_eq]
      exact Subgroup.mul_mem _ hjP1 hp_inv
    exact q13d_lam_not_mem_E0 h (q13d_I_P1_le_E0 h hlamP1)

theorem q13d_I_W_card (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G))
    (hlo : lam * om * lam⁻¹ = om) {j : G} (hj : j ∈ lam • ((q13A t tau x₁ x₂ rho
      ⊔ closure ({tau, om} : Set G) : Subgroup G) : Set G)) (hj2 : j * j = 1) :
    CFSG.Open.IsElemAbelian 2 (closure ({j, tau, om, (x₁ * x₂) ^ 2} : Set G)) ∧
      Nat.card ↥(closure ({j, tau, om, (x₁ * x₂) ^ 2} : Set G)) = 16 := by
  let z : G := (x₁ * x₂) ^ 2
  have hzdef : z = (x₁ * x₂) ^ 2 := rfl
  change CFSG.Open.IsElemAbelian 2 (closure ({j, tau, om, z} : Set G)) ∧
    Nat.card ↥(closure ({j, tau, om, z} : Set G)) = 16
  have hcomm := dI3b_comm h hI hlo hj
  have hjtau : j * tau = tau * j := hcomm.1
  have hjom : j * om = om * j := hcomm.2.1
  have hjz : j * z = z * j := hcomm.2.2.1
  have hjP1 : j ∉ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) : Subgroup G) :=
    hcomm.2.2.2
  have hK_le_CO : closure ({tau, om} : Set G) ≤ closure ({t, om} : Set G) := by
    rw [← hI]; exact inf_le_left
  have hP1c := q13d_I_P1_comm h hI
  have htau_mem : tau ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hom_mem : om ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hzA : z ∈ q13A t tau x₁ x₂ rho := by
    rw [hzdef]
    exact q13a_V_le_A h (Subgroup.subset_closure (by simp))
  have hz_mem : z ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) : Subgroup G) :=
    Subgroup.mem_sup_left hzA
  have hto : tau * om = om * tau := hP1c tau htau_mem om hom_mem
  have htz : tau * z = z * tau := hP1c tau htau_mem z hz_mem
  have hoz : om * z = z * om := hP1c om hom_mem z hz_mem
  have hz2 : z * z = 1 := (q13b_z_facts h).2
  have hz1 : z ≠ 1 := (q13b_z_facts h).1
  have hWel : CFSG.Open.IsElemAbelian 2 (closure ({j, tau, om, z} : Set G)) := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute (p := 2) ?_ ?_
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
        simp [hjtau, hjom, hjz, hto, htz, hoz]
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · rw [pow_two]; exact hj2
      · rw [pow_two]; exact q13a_tau_mul_self h
      · rw [pow_two]; exact h.om_sq
      · rw [pow_two]; exact hz2
  have hKcard : Nat.card ↥(closure ({tau, om} : Set G)) = 4 := by
    have hnorm : ∀ k ∈ closure ({tau, om} : Set G), ∀ aa ∈ q13A t tau x₁ x₂ rho,
        k * aa * k⁻¹ ∈ q13A t tau x₁ x₂ rho := by
      intro k hk aa haa
      have hc : k * aa = aa * k :=
        (hP1c aa (Subgroup.mem_sup_left haa) k (Subgroup.mem_sup_right hk)).symm
      have heq : k * aa * k⁻¹ = aa := by rw [hc]; group
      rw [heq]; exact haa
    have hbot : q13A t tau x₁ x₂ rho ⊓ closure ({tau, om} : Set G) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨hxA, hxK⟩ := Subgroup.mem_inf.mp hx
      exact q13d_A_inf_CO h x hxA (hK_le_CO hxK)
    have hcs := card_sup_eq_mul (H := q13A t tau x₁ x₂ rho)
      (K := closure ({tau, om} : Set G)) hnorm hbot
    rw [q13d_I_card_P1 h hI, q13a_card_A h] at hcs
    norm_num at hcs
    omega
  have hzpcard : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hK3card : Nat.card ↥(closure ({tau, om, z} : Set G)) = 8 := by
    have hzK : z ∉ closure ({tau, om} : Set G) := by
      intro hzK
      exact hz1 (q13d_A_inf_CO h z hzA (hK_le_CO hzK))
    have hbot : closure ({tau, om} : Set G) ⊓ Subgroup.zpowers z = ⊥ := by
      rw [inf_comm]
      exact dI3b_inf_zpowers_eq_bot hz2 hz1 hzK
    have hnorm : ∀ k ∈ Subgroup.zpowers z, ∀ aa ∈ closure ({tau, om} : Set G),
        k * aa * k⁻¹ ∈ closure ({tau, om} : Set G) := by
      intro k hk aa haa
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      have hza : z * aa = aa * z := hP1c z hz_mem aa (Subgroup.mem_sup_right haa)
      have hcz : Commute (z ^ n) aa := ((show Commute z aa from hza).zpow_left n)
      have heq : z ^ n * aa * (z ^ n)⁻¹ = aa := by
        rw [hcz.eq]; group
      rw [heq]; exact haa
    have hK3eq : closure ({tau, om, z} : Set G) =
        closure ({tau, om} : Set G) ⊔ Subgroup.zpowers z := by
      rw [show ({tau, om, z} : Set G) = ({tau, om} : Set G) ∪ ({z} : Set G) by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto]
      rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
    rw [hK3eq, card_sup_eq_mul hnorm hbot]
    norm_num [hKcard, hzpcard]
  have hK3_le_W : closure ({tau, om, z} : Set G) ≤ closure ({j, tau, om, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hK3_le_P1 : closure ({tau, om, z} : Set G) ≤
      (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) : Subgroup G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left hzA
  have hj1 : j ≠ 1 := fun h1 => hjP1 (h1 ▸ Subgroup.one_mem _)
  have hjK3 : j ∉ closure ({tau, om, z} : Set G) := fun hh => hjP1 (hK3_le_P1 hh)
  have hzpjcard : Nat.card ↥(Subgroup.zpowers j) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hj2) hj1
  have hbotj : Subgroup.zpowers j ⊓ closure ({tau, om, z} : Set G) = ⊥ :=
    dI3b_inf_zpowers_eq_bot hj2 hj1 hjK3
  have hnormj : ∀ k ∈ closure ({tau, om, z} : Set G), ∀ hh ∈ Subgroup.zpowers j,
      k * hh * k⁻¹ ∈ Subgroup.zpowers j := by
    intro k hk hh hhh
    have hkW : k ∈ closure ({j, tau, om, z} : Set G) := hK3_le_W hk
    have hhW : hh ∈ closure ({j, tau, om, z} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hhh
    have hc : k * hh = hh * k := CFSG.Open.IsElemAbelian.comm hWel hkW hhW
    have heq : k * hh * k⁻¹ = hh := by rw [hc]; group
    rw [heq]; exact hhh
  have hWcard : Nat.card ↥(Subgroup.zpowers j ⊔ closure ({tau, om, z} : Set G)) = 16 := by
    rw [card_sup_eq_mul hnormj hbotj]
    norm_num [hzpjcard, hK3card]
  have hW_eq : closure ({j, tau, om, z} : Set G) =
      Subgroup.zpowers j ⊔ closure ({tau, om, z} : Set G) := by
    rw [show ({j, tau, om, z} : Set G) = ({j} : Set G) ∪ ({tau, om, z} : Set G) by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
  refine ⟨hWel, ?_⟩
  rw [hW_eq]
  exact hWcard

theorem q13d_I_lamP1_not_tG (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G))
    (hlo : lam * om * lam⁻¹ = om) :
    ∀ p ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)), (lam * p) * (lam * p)
      = 1 → ∀ g : G, g * t * g⁻¹ ≠ lam * p := by
  intro p hp hp2 g hg
  let z : G := (x₁ * x₂) ^ 2
  have hzdef : z = (x₁ * x₂) ^ 2 := rfl
  obtain ⟨a, haA, hlam_a, haa⟩ := q13d_exists_a_sq_z h
  have haz : z = a * a := haa.symm
  have hjmem : lam * p ∈ lam • ((q13A t tau x₁ x₂ rho
      ⊔ closure ({tau, om} : Set G) : Subgroup G) : Set G) := by
    rw [Set.mem_smul_set]
    exact ⟨p, hp, by rw [smul_eq_mul]⟩
  have hWfacts := q13d_I_W_card h hI hlo hjmem hp2
  have hW : CFSG.Open.IsElemAbelian 2 (closure ({lam * p, tau, om, z} : Set G)) := hWfacts.1
  have hWcard : Nat.card ↥(closure ({lam * p, tau, om, z} : Set G)) = 16 := hWfacts.2
  have hjW : lam * p ∈ closure ({lam * p, tau, om, z} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hWj : ∀ w ∈ closure ({lam * p, tau, om, z} : Set G),
      w * (lam * p) = (lam * p) * w :=
    fun w hw => CFSG.Open.IsElemAbelian.comm hW hw hjW
  have hla : a * lam = lam * a := by
    calc a * lam = (lam * a * lam⁻¹) * lam := by rw [hlam_a]
      _ = lam * a := by group
  have hpa : a * p = p * a := q13d_I_P1_comm h hI a (Subgroup.mem_sup_left haA) p hp
  have haj : a * (lam * p) = (lam * p) * a := by
    calc a * (lam * p) = (a * lam) * p := by group
      _ = (lam * a) * p := by rw [hla]
      _ = lam * (a * p) := by group
      _ = lam * (p * a) := by rw [hpa]
      _ = (lam * p) * a := by group
  have hatau : a * tau = tau * a := q13d_A_cent_tau h a haA
  have haom : a * om = om * a := (q13d_I_om_cent_A h hI a haA).symm
  have hazA : z ∈ q13A t tau x₁ x₂ rho := by
    rw [hzdef]
    exact q13a_V_le_A h (Subgroup.subset_closure (by simp))
  have haz' : a * z = z * a := q13a_A_comm h a haA z hazA
  have haW : ∀ w ∈ closure ({lam * p, tau, om, z} : Set G), a * w = w * a := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact haj
        · exact hatau
        · exact haom
        · exact haz'
    | one => simp
    | mul x y hx hy ihx ihy =>
        rw [← mul_assoc, ihx, mul_assoc, ihy, ← mul_assoc]
    | inv x hx ihx =>
        calc a * x⁻¹ = x⁻¹ * (x * a) * x⁻¹ := by group
          _ = x⁻¹ * (a * x) * x⁻¹ := by rw [← ihx]
          _ = x⁻¹ * a := by group
  have ha4 : a ^ 4 = 1 := by
    have h4 : a ^ 4 = (a * a) * (a * a) := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    rw [h4, haa, (q13b_z_facts h).2]
  have ha2 : IsPGroup 2 ↥(Subgroup.zpowers a ⊔ closure ({lam * p, tau, om, z} : Set G)) := by
    refine IsPGroup.to_sup_of_normal_right' ?_ ?_ ?_
    · exact IsPGroup.of_card_dvd_pow (n := 2) (by
        rw [Nat.card_zpowers, show (2 : ℕ) ^ 2 = 4 by norm_num]
        exact orderOf_dvd_of_pow_eq_one ha4)
    · exact hW.isPGroup
    · refine Subgroup.zpowers_le.mpr ?_
      exact Subgroup.mem_normalizer_fintype (fun w hw => by
        have heq : a * w * a⁻¹ = w := by rw [haW w hw]; group
        rw [heq]; exact hw)
  have haW' : a ∈ closure ({lam * p, tau, om, z} : Set G) :=
    q13d_E16_cent_le h ⟨g, hg⟩ hW hWcard hWj haj haW ha2
  have haa1 : a * a = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hW haW'
  have hz1 : z ≠ 1 := (q13b_z_facts h).1
  exact hz1 (by rw [haz, haa1])

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
