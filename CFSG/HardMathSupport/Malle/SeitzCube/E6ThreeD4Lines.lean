module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Main
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Assembly

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.SeitzGeneration CFSG.Open
open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator (PhiPlaneGenAt)

open CFSG.RankThree.PartOne.CTP (ExtSeitzAtInnerFor)

open scoped MatrixGroups

section Mix

variable {C : Type*} [Group C] {K : Type} [Field K]
  {ψ : Fin 3 → SL(3, K) →* C} {g : SL(3, K)} {p : ℕ}

theorem mix_ne (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) (hp : p.Prime) (hp3 : p ≠ 3)
    (hg : orderOf g = p) (y : ℕ) (k : ℤ) : ψ 0 g * ψ 1 (g ^ y) ≠ ψ 2 g ^ k := by
  intro h
  have h0 : ψ 0 g = ψ 2 g ^ k * (ψ 1 (g ^ y))⁻¹ := by
    rw [← h]; group
  have hc : ∀ A, Commute (ψ 0 (g ^ (1 : ℤ))) (ψ 0 A) := by
    intro A
    rw [zpow_one, h0]
    have h2 : Commute (ψ 2 g ^ k) (ψ 0 A) :=
      ((hcomm 2 0 (by decide) g A).zpow_left k)
    have h1 : Commute (ψ 1 (g ^ y))⁻¹ (ψ 0 A) := (hcomm 1 0 (by decide) _ A).inv_left
    exact h2.mul_left h1
  have := dvd_of_commute_range hinj hp hp3 hg 0 1 hc
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

end Mix

theorem disjoint_zpowers_of_orderOf_prime {G : Type*} [Group G] {a b : G} {p : ℕ}
    (hp : p.Prime) (hb : orderOf b = p) (hba : b ∉ Subgroup.zpowers a) :
    Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b) := by
  rw [disjoint_comm]
  haveI : Finite (Subgroup.zpowers b) :=
    finite_zpowers.2 (orderOf_pos_iff.1 (hb ▸ hp.pos))
  have hcard : Nat.card (Subgroup.zpowers b ⊓ Subgroup.zpowers a : Subgroup G) ∣ p := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers b ⊓ Subgroup.zpowers a ≤
      Subgroup.zpowers b)
    rwa [Nat.card_zpowers, hb] at this
  rcases (Nat.dvd_prime hp).1 hcard with h1 | h1
  · rw [disjoint_iff]
    exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : Subgroup.zpowers b ⊓ Subgroup.zpowers a = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, Nat.card_zpowers, hb])
    have hb' : b ∈ Subgroup.zpowers b ⊓ Subgroup.zpowers a := by
      rw [heq]; exact Subgroup.mem_zpowers b
    exact hba (Subgroup.mem_inf.1 hb').2

section Main


theorem e6ThreeD4Lines_of
    (hphi : ∀ r : ℕ, r ≠ 3 → PhiPlaneGenAt 1 r)
    (hext : ∀ q : TauCeti.PrimePower, q.p = 2 →
      ExtSeitzAtInnerFor (TauCeti.LieTypeIndex.trialityD4 q) fun _ => True)
    (hfs : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
      Finite (Cat ⟨.trialityD4 q, hv⟩) ∧ IsSimpleGroup (Cat ⟨.trialityD4 q, hv⟩)) :
    E6ThreeD4Lines := by
  intro K _ _ r _ _ ψ hψ hinj hcomm p g hp hp3 hpr hpq hg s hs u hu he
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self (Nat.card K)
    obtain ⟨c, hc⟩ := hpq
    have : Nat.card K ^ 2 + Nat.card K = Nat.card K * (Nat.card K + 1) := by ring
    omega
  have hp5 : 5 ≤ p := by
    by_contra h
    have h2 := hp.two_le
    have : p = 2 ∨ p = 3 ∨ p = 4 := by omega
    rcases this with h | h | h
    · exact hp2 h
    · exact hp3 h
    · rw [h] at hp; norm_num at hp
  obtain ⟨Y, hY1, hY2, hY3, hY4, ⟨q', hqc, hqp, hiso⟩, hcen⟩ :=
    exists_d4Line_layer hψ hp hp3 hpr hpq hg ⟨s, hs⟩
  have huY : u ∈ Y := by
    rcases hu with hu | hu
    · exact hY2 (parabolicRadicalRoots Tag.E6 (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1))
        (fun α hα => (mem_parabolicRadicalRoots_iff.1 hα).1)
        (fun F _ a v hv hva => mem_rootSpan_radical_inter_of_mem_centralizer hv hva)
        (fun F _ => (parabolicLevi_le_parabolicSubgroup _).trans
          (parabolicSubgroup_le_normalizer_parabolicRadical _)) u hu he
    · exact hY2 (negRadicalRoots Tag.E6 (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1))
        (fun α hα => isRoot_of_mem_negRadicalRoots hα)
        (fun F _ a v hv hva => mem_rootSpan_negRadicalRoots_inter_of_mem_centralizer hv hva)
        (fun F _ => parabolicLevi_le_normalizer_negRadical F _) u hu he
  set m : ℕ := Nat.card K ^ s with hm
  set e : adjointGroup Tag.E6 K := ψ 0 g * ψ 1 (g ^ m) with he_def
  set e' : adjointGroup Tag.E6 K := ψ 0 g * ψ 1 (g ^ ((p - 1) * m)) with he'_def
  have hab := isElemAbelian_cube hinj hcomm hp hp3 hg
  have hcube := card_cube hinj hcomm hp hp3 hg
  have hcc : ∀ a ∈ cube ψ g, ∀ b ∈ cube ψ g, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hψ1 : ∀ y : ℕ, ψ 1 (g ^ y) ∈ cube ψ g := fun y => by
    rw [map_pow]; exact Subgroup.pow_mem _ (mem_cube 1) y
  have hmix : ∀ y : ℕ, ψ 0 g * ψ 1 (g ^ y) ∈ cube ψ g := fun y =>
    Subgroup.mul_mem _ (mem_cube 0) (hψ1 y)
  have hecube : e ∈ cube ψ g := hmix m
  have he'cube : e' ∈ cube ψ g := hmix _
  have hord : ∀ x ∈ cube ψ g, x ≠ 1 → orderOf x = p := fun x hx hx1 =>
    orderOf_eq_prime (hab.2 x hx) hx1
  have heord : orderOf e = p := hord e hecube (by
    have := mix_ne hinj hcomm hp hp3 hg m 0
    rwa [zpow_zero] at this)
  have he'ord : orderOf e' = p := hord e' he'cube (by
    have := mix_ne hinj hcomm hp hp3 hg ((p - 1) * m) 0
    rwa [zpow_zero] at this)
  have haord : orderOf (ψ 2 g) = p := hord _ (mem_cube 2) (fun h1 => by
    have : g = 1 := hinj 2 (by rw [h1, map_one])
    rw [this, orderOf_one] at hg
    exact hp.ne_one hg.symm)
  have hBle : Subgroup.zpowers e ≤ cube ψ g := Subgroup.zpowers_le.2 hecube
  have hB : Nat.card (Subgroup.zpowers e) = p := by rw [Nat.card_zpowers, heord]
  have hBY : Disjoint (Subgroup.zpowers e) Y := by
    rw [Subgroup.disjoint_def]
    intro x hxB hxY
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxB
    refine hcen _ hxY ?_
    intro z hz
    exact ((hY1 z hz).zpow_right n).eq
  have hcent : ∀ y ∈ Y, ∀ b ∈ Subgroup.zpowers e, Commute y b := fun y hy b hb => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (hY1 y hy).zpow_right n
  have hE'le : Subgroup.zpowers (ψ 2 g) ⊔ Subgroup.zpowers e' ≤ cube ψ g :=
    sup_le (Subgroup.zpowers_le.2 (mem_cube 2)) (Subgroup.zpowers_le.2 he'cube)
  have hE'Y : Subgroup.zpowers (ψ 2 g) ⊔ Subgroup.zpowers e' ≤ Y :=
    sup_le (Subgroup.zpowers_le.2 hY3) (Subgroup.zpowers_le.2 hY4)
  have hdisj : Disjoint (Subgroup.zpowers (ψ 2 g)) (Subgroup.zpowers e') :=
    disjoint_zpowers_of_orderOf_prime hp he'ord (fun hmem => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact mix_ne hinj hcomm hp hp3 hg ((p - 1) * m) k hk.symm)
  have hcommZ : ∀ x ∈ Subgroup.zpowers (ψ 2 g), ∀ y ∈ Subgroup.zpowers e', Commute x y :=
    fun x hx y hy => hcc x (Subgroup.zpowers_le.2 (mem_cube 2) hx) y
      (Subgroup.zpowers_le.2 he'cube hy)
  have hE'card : Nat.card ↥(Subgroup.zpowers (ψ 2 g) ⊔ Subgroup.zpowers e') = p ^ 2 := by
    rw [card_sup_of_commute _ _ hcommZ hdisj, Nat.card_zpowers, Nat.card_zpowers, haord, he'ord]
    ring
  have hgen : PlaneGen ↥Y p := by
    refine planeGen_of_isoLie hiso hp5 (by rw [hqp]; exact hpr) ?_
      (fun _ => hphi p hp3) (fun h2 => hext q' h2) ?_
    · rw [hqc]
      have := Int.natCast_dvd_natCast.2 hpq
      push_cast at this
      simpa using this
    · intro h2
      obtain ⟨hv, ⟨f⟩⟩ := hiso
      obtain ⟨hfin, hsim⟩ := hfs q' hv h2
      haveI : IsSimpleGroup (Cat ⟨.trialityD4 q', hv⟩) := hsim
      exact ⟨Finite.of_equiv _ f.symm.toEquiv, f.isSimpleGroup⟩
  exact le_hyperClosure_of_planeGen hab hcube hBle hB hBY hcent hE'le hE'Y hE'card hgen huY

end Main

end CFSG.HardMathSupport.Malle.SeitzCube
