module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.GroupLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.CentralCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Orbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ComponentOrder

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open scoped commutatorElement

variable {H : Type} [Group H]

theorem isCompIn_le_or_le_centralizer [Finite H] {Z X S : Subgroup H} (hZ : IsCompIn Z X)
    (hSX : S ≤ X) (hS : (S.subgroupOf X).IsSubnormal) :
    Z ≤ S ∨ Z ≤ centralizer (S : Set H) := by
  rcases CFSG.LocalCores.component_subnormal_subgroup hZ.2 hS with h | h
  · left
    intro x hx
    exact (show (⟨x, hZ.1 hx⟩ : ↥X) ∈ S.subgroupOf X from h hx)
  · right
    have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hZ.1 h
    rw [inf_eq_left.2 hSX] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1

theorem sup_le_normalizer_of_commute {A B : Subgroup H} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ⊔ B ≤ normalizer (A : Set H) :=
  sup_le Subgroup.le_normalizer fun b hb =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha => hAB a ha b hb)

theorem isCompIn_le_or_le_of_commute [Finite H] {K A B : Subgroup H} (hK : IsCompIn K (A ⊔ B))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : K ≤ A ∨ K ≤ B := by
  have hA : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le_normalizer_of_commute hAB)
  have hB : (B.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
      (by rw [sup_comm]; exact sup_le_normalizer_of_commute fun b hb a ha => (hAB a ha b hb).symm)
  by_contra hcon
  push Not at hcon
  have h1 := (isCompIn_le_or_le_centralizer hK le_sup_left hA.isSubnormal).resolve_left hcon.1
  have h2 := (isCompIn_le_or_le_centralizer hK le_sup_right hB.isSubnormal).resolve_left hcon.2
  refine not_forall_commute_of_isQuasisimple hK.isQuasisimple fun a ha b hb => ?_
  have := le_centralizer_sup h1 h2 hb
  exact mem_centralizer_iff.1 this a (hK.1 ha)

theorem commutatorElement_mem {P : Subgroup H} {a b : H} (ha : a ∈ P) (hb : b ∈ P) :
    ⁅a, b⁆ ∈ P := by
  simp only [commutatorElement_def]
  exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)

theorem commutator_fixed_aux {P Q : Subgroup H} (hPQ : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a)
    {a a' z z' : H} (ha : a ∈ P) (ha' : a' ∈ P) (hz : z ∈ P ⊓ Q) (hz' : z' ∈ P ⊓ Q) :
    ⁅a * z, a' * z'⁆ = ⁅a, a'⁆ := by
  have h1 : z * (a' * z') = (a' * z') * z := by
    calc z * (a' * z') = (z * a') * z' := by group
      _ = (a' * z) * z' := by rw [(hPQ a' ha' z hz.2).symm]
      _ = a' * (z * z') := by group
      _ = a' * (z' * z) := by rw [hPQ z hz.1 z' hz'.2]
      _ = (a' * z') * z := by group
  rw [commutatorElement_mul_of_commute h1, commutatorElement_of_commute_mul (hPQ a ha z' hz'.2)]

theorem le_sup_fixed_of_commute {P Q U K : Subgroup H}
    (hPQ : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) (hUP : U ≤ normalizer (P : Set H))
    (hUQ : U ≤ normalizer (Q : Set H)) (hK : ⁅K, K⁆ = K) (hKPQ : K ≤ P ⊔ Q)
    (hKU : K ≤ centralizer (U : Set H)) :
    K ≤ (P ⊓ centralizer (U : Set H)) ⊔ (Q ⊓ centralizer (U : Set H)) := by
  have key : ∀ a ∈ P, ∀ b ∈ Q, a * b ∈ K → ∀ u ∈ U, ∃ z ∈ P ⊓ Q,
      u * a * u⁻¹ = a * z ∧ u * b * u⁻¹ = z⁻¹ * b := by
    intro a ha b hb hx u hu
    have hxu : u * (a * b) = (a * b) * u := mem_centralizer_iff.1 (hKU hx) u hu
    have haP : u * a * u⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hUP hu) a).1 ha
    have hbQ : u * b * u⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hUQ hu) b).1 hb
    have hx' : (u * a * u⁻¹) * (u * b * u⁻¹) = a * b := by
      calc (u * a * u⁻¹) * (u * b * u⁻¹) = u * (a * b) * u⁻¹ := by group
        _ = a * b := by rw [hxu]; group
    have hzQ : a⁻¹ * (u * a * u⁻¹) = b * (u * b * u⁻¹)⁻¹ := by
      calc a⁻¹ * (u * a * u⁻¹)
          = a⁻¹ * ((u * a * u⁻¹) * (u * b * u⁻¹)) * (u * b * u⁻¹)⁻¹ := by group
        _ = a⁻¹ * (a * b) * (u * b * u⁻¹)⁻¹ := by rw [hx']
        _ = b * (u * b * u⁻¹)⁻¹ := by group
    refine ⟨a⁻¹ * (u * a * u⁻¹), ⟨P.mul_mem (P.inv_mem ha) haP, ?_⟩, by group, ?_⟩
    · rw [hzQ]
      exact Q.mul_mem hb (Q.inv_mem hbQ)
    · refine mul_left_cancel (a := a * (a⁻¹ * (u * a * u⁻¹))) ?_
      calc a * (a⁻¹ * (u * a * u⁻¹)) * (u * b * u⁻¹) = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
        _ = a * b := hx'
        _ = a * (a⁻¹ * (u * a * u⁻¹)) * ((a⁻¹ * (u * a * u⁻¹))⁻¹ * b) := by group
  calc K = ⁅K, K⁆ := hK.symm
    _ ≤ _ := by
      refine commutator_le.2 fun x hx y hy => ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hPQ (hKPQ hx)
      obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup_of_commute hPQ (hKPQ hy)
      rw [commutatorElement_mul_mul hPQ ha ha' hb hb']
      have hQP : ∀ b ∈ Q, ∀ a ∈ P, b * a = a * b := fun b hb a ha => (hPQ a ha b hb).symm
      refine Subgroup.mul_mem_sup ⟨commutatorElement_mem ha ha', ?_⟩
        ⟨commutatorElement_mem hb hb', ?_⟩
      · refine mem_centralizer_iff.2 fun u hu => ?_
        obtain ⟨z, hz, hza, -⟩ := key a ha b hb hx u hu
        obtain ⟨z', hz', hza', -⟩ := key a' ha' b' hb' hy u hu
        have e : u * ⁅a, a'⁆ * u⁻¹ = ⁅a, a'⁆ := by
          calc u * ⁅a, a'⁆ * u⁻¹ = ⁅u * a * u⁻¹, u * a' * u⁻¹⁆ := by
                simp only [commutatorElement_def]; group
            _ = ⁅a * z, a' * z'⁆ := by rw [hza, hza']
            _ = ⁅a, a'⁆ := commutator_fixed_aux hPQ ha ha' hz hz'
        calc u * ⁅a, a'⁆ = (u * ⁅a, a'⁆ * u⁻¹) * u := by group
          _ = ⁅a, a'⁆ * u := by rw [e]
      · refine mem_centralizer_iff.2 fun u hu => ?_
        obtain ⟨z, hz, -, hzb⟩ := key a ha b hb hx u hu
        obtain ⟨z', hz', -, hzb'⟩ := key a' ha' b' hb' hy u hu
        have hz1 : z⁻¹ ∈ Q ⊓ P := ⟨Q.inv_mem hz.2, P.inv_mem hz.1⟩
        have hz1' : z'⁻¹ ∈ Q ⊓ P := ⟨Q.inv_mem hz'.2, P.inv_mem hz'.1⟩
        have c1 : z⁻¹ * b = b * z⁻¹ := (hQP b hb z⁻¹ hz1.2).symm
        have c2 : z'⁻¹ * b' = b' * z'⁻¹ := (hQP b' hb' z'⁻¹ hz1'.2).symm
        have e : u * ⁅b, b'⁆ * u⁻¹ = ⁅b, b'⁆ := by
          calc u * ⁅b, b'⁆ * u⁻¹ = ⁅u * b * u⁻¹, u * b' * u⁻¹⁆ := by
                simp only [commutatorElement_def]; group
            _ = ⁅b * z⁻¹, b' * z'⁻¹⁆ := by rw [hzb, hzb', c1, c2]
            _ = ⁅b, b'⁆ := commutator_fixed_aux hQP hb hb' hz1 hz1'
        calc u * ⁅b, b'⁆ = (u * ⁅b, b'⁆ * u⁻¹) * u := by group
          _ = ⁅b, b'⁆ * u := by rw [e]

theorem le_normalizer_of_map_conj_le {Q S : Subgroup H}
    (h : ∀ g ∈ S, Q.map (MulAut.conj g).toMonoidHom ≤ Q) : S ≤ normalizer (Q : Set H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h g hg ⟨x, hx, rfl⟩
  · intro hx
    have := h g⁻¹ (S.inv_mem hg) ⟨_, hx, rfl⟩
    simpa [mul_assoc] using this

theorem exists_isCompIn_le_conjClosure [Finite H] {T W K : Subgroup H}
    (hWT : W ≤ normalizer (T : Set H))
    (hK : IsCompIn K (centralizer ((W ⊔ T : Subgroup H) : Set H)))
    (hKL : K ≤ layerIn (centralizer (T : Set H))) :
    ∃ M : Subgroup H, IsCompIn M (centralizer (T : Set H)) ∧ K ≤ conjClosure M W := by
  set C : Subgroup H := centralizer (T : Set H) with hC
  have hWC : W ≤ normalizer (C : Set H) := fun g hg =>
    mem_normalizer_centralizer_of_mem_normalizer (hWT hg)
  have hKq := hK.isQuasisimple
  obtain ⟨M, hM, hKM⟩ : ∃ M, IsCompIn M C ∧ ¬ K ≤ centralizer (M : Set H) := by
    by_contra hcon
    push Not at hcon
    have h1 : layerIn C ≤ centralizer (K : Set H) := layerIn_le_iff.2 fun E hE x hx =>
      mem_centralizer_iff.2 fun k hk => (mem_centralizer_iff.1 (hcon E hE hk) x hx).symm
    exact not_forall_commute_of_isQuasisimple hKq fun a ha b hb =>
      (mem_centralizer_iff.1 (h1 (hKL ha)) b hb).symm
  refine ⟨M, hM, ?_⟩
  set P : Subgroup H := conjClosure M W with hP
  set 𝒬 : Set (Subgroup H) :=
    {E | IsCompIn E C ∧ ∀ w ∈ W, E ≠ M.map (MulAut.conj w).toMonoidHom} with h𝒬
  set Q : Subgroup H := sSup 𝒬 with hQ
  have hconjM : ∀ w ∈ W, IsCompIn (M.map (MulAut.conj w).toMonoidHom) C := fun w hw =>
    isCompIn_map_conj_of_mem_normalizer hM (hWC hw)
  have hlayer : layerIn C ≤ P ⊔ Q := by
    refine layerIn_le_iff.2 fun E hE => ?_
    by_cases h : ∃ w ∈ W, E = M.map (MulAut.conj w).toMonoidHom
    · obtain ⟨w, hw, rfl⟩ := h
      exact le_sup_of_le_left (map_conj_le_conjClosure hw)
    · push Not at h
      exact le_sup_of_le_right (le_sSup ⟨hE, h⟩)
  have hQM : ∀ w ∈ W,
      Q ≤ centralizer ((M.map (MulAut.conj w).toMonoidHom : Subgroup H) : Set H) := by
    intro w hw
    refine sSup_le fun E hE e he => mem_centralizer_iff.2 fun m hm => ?_
    exact (hconjM w hw).commute_of_ne hE.1 (fun h => hE.2 w hw h.symm) m hm e he
  have hPQ : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a := by
    have hPQ' : P ≤ centralizer (Q : Set H) := iSup₂_le fun w hw a ha =>
      mem_centralizer_iff.2 fun b hb => (mem_centralizer_iff.1 (hQM w hw hb) a ha).symm
    exact fun a ha b hb => (mem_centralizer_iff.1 (hPQ' ha) b hb).symm
  have hPC : P ≤ C := conjClosure_le_of_le_normalizer hM.1 hWC
  have hQC : Q ≤ C := sSup_le fun E hE => hE.1.1
  have hTN : ∀ R : Subgroup H, R ≤ C → T ≤ normalizer (R : Set H) := fun R hR t ht =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun r hr =>
      (mem_centralizer_iff.1 (hR hr) t ht).symm)
  have hmem : ∀ w ∈ W, ∀ E ∈ 𝒬, E.map (MulAut.conj w).toMonoidHom ∈ 𝒬 := by
    intro w hw E hE
    refine ⟨isCompIn_map_conj_of_mem_normalizer hE.1 (hWC hw), fun w' hw' h => hE.2 (w⁻¹ * w')
      (W.mul_mem (W.inv_mem hw) hw') ?_⟩
    have h2 := congrArg (fun A : Subgroup H => A.map (MulAut.conj w⁻¹).toMonoidHom) h
    simp only [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h2
    exact h2
  have hUP : W ⊔ T ≤ normalizer (P : Set H) := sup_le (le_normalizer_conjClosure M W) (hTN P hPC)
  have hUQ : W ⊔ T ≤ normalizer (Q : Set H) := by
    refine sup_le (le_normalizer_of_map_conj_le fun w hw => ?_) (hTN Q hQC)
    exact Subgroup.map_le_iff_le_comap.2 (sSup_le fun E hE =>
      Subgroup.map_le_iff_le_comap.1 (le_sSup (hmem w hw E hE)))
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 hKq.1
  have hfix := le_sup_fixed_of_commute hPQ hUP hUQ hKperf (hKL.trans hlayer) hK.1
  have hcomp : IsCompIn K ((P ⊓ centralizer ((W ⊔ T : Subgroup H) : Set H)) ⊔
      (Q ⊓ centralizer ((W ⊔ T : Subgroup H) : Set H))) :=
    isCompIn_of_le hK hfix (sup_le inf_le_right inf_le_right)
  rcases isCompIn_le_or_le_of_commute hcomp (fun a ha b hb => hPQ a ha.1 b hb.1) with h | h
  · exact h.trans inf_le_left
  · exfalso
    refine hKM fun k hk => mem_centralizer_iff.2 fun m hm => ?_
    exact (hPQ m (le_conjClosure M W hm) k (h.trans inf_le_left hk))
