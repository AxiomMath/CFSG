module

public import CFSG.CGT.T75Q.Good
public import CFSG.CGT.T75Q.ZCenter

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 CFSG.CGT.T75P

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem ugen_le_closure_classD_inter :
    ugen T ≤ Subgroup.closure (classD T ∩ ((ugen T : Subgroup G) : Set G)) :=
  Subgroup.closure_mono fun _ hx => ⟨gammaD_subset_classD hx, gammaD_subset_ugen hx⟩

theorem Std82.hclU (s : Std82 T T₁) :
    Subgroup.normalClosure ((T.subgroupOf (ugen T) : Subgroup ↥(ugen T)) : Set ↥(ugen T)) = ⊤ :=
  s.normalClosure_top_of_gen le_rfl ugen_le_closure_classD_inter

theorem Std82.Z (s : Std82 T T₁) :
    ∀ c ∈ ugen T ⊓ Subgroup.centralizer (ugen T : Set G), c * c = 1 → c = 1 := by
  intro c hc hcc
  have hfin : Finite G := s.finite
  have hodd := odd_card_center_of_good s.wc s.hTH s.hHU s.hHN s.hHC s.htrans s.hH2 s.hprod
    s.hinf s.hCU s.hclU
  have hzc : (⟨c, hc.1⟩ : ↥(ugen T)) ∈ Subgroup.center ↥(ugen T) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc.2 g.1 g.2)
  let z : ↥(Subgroup.center ↥(ugen T)) := ⟨⟨c, hc.1⟩, hzc⟩
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [pow_two] using hcc
  have hoddord : Odd (orderOf z) := hodd.of_dvd_nat (orderOf_dvd_natCard z)
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
  have h1 : orderOf z = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hoddord
      exact absurd hoddord (by decide)
  have hz1 : z = 1 := orderOf_eq_one_iff.1 h1
  have h3 : (((z : ↥(Subgroup.center ↥(ugen T))) : ↥(ugen T)) : G) = 1 := by
    rw [hz1]
    rfl
  exact h3

section Certified



theorem Std82.F1 (s : Std82 T T₁) (h215 : Lemma215Stmt) (hL : ListWCIdentification) :
    ∀ c ∈ Subgroup.centralizer (ugen T : Set G), c ≠ 1 → ∀ d ∈ classD T, c * d = d * c →
      d ∈ ugen T := by
  intro c hcU hc1 d hd hcd
  classical
  have hfin : Finite G := s.finite
  have hcH : c ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) := by
    rw [s.hCeq]
    exact hcU
  set Y : Subgroup G := Subgroup.closure {x | x ∈ classD T ∧ c * x = x * c} with hYdef
  have hUY : ugen T ≤ Y := by
    rw [ugen, Subgroup.closure_le]
    intro x hx
    exact Subgroup.subset_closure ⟨hx.1,
      gammaD_le_centralizer s.h1 s.h62 s.h63 s.h66 s.hc s.hnat chain4 (by norm_num) hcH x hx⟩
  have hdY : d ∈ Y := Subgroup.subset_closure ⟨hd, hcd⟩
  have hcY : c ∈ Subgroup.centralizer (Y : Set G) := by
    have hle : Y ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [hYdef, Subgroup.closure_le]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.2 hx.2.symm
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hu)
  have hYtop : Y ≠ ⊤ := s.ne_top_of_centralizer hcY hc1
  have hUtop : ugen T ≠ ⊤ := s.ne_top_of_centralizer hcU hc1
  have hgenY : Y ≤ Subgroup.closure (classD T ∩ (Y : Set G)) :=
    Subgroup.closure_mono fun x hx => ⟨hx.1, Subgroup.subset_closure hx⟩
  have hclY := s.normalClosure_top_of_gen hUY hgenY
  obtain ⟨hker, hsurj⟩ := s.jMap_surj h215 hL hUY hUtop hYtop s.hclU hclY
  exact s.mem_ugen_of_surj hUY hker hsurj hd hdY

theorem Std82.endHyp (s : Std82 T T₁) (h215 : Lemma215Stmt) (hL : ListWCIdentification) :
    EndHyp T (ugen T) :=
  endHyp_ugen s.hc s.h66 (by norm_num) (s.F1 h215 hL) s.Z

end Certified

end CFSG.CGT.T75Q
