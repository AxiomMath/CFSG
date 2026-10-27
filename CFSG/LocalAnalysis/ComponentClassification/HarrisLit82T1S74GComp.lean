module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GSetup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RC

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

theorem isSubnormal_subgroupOf_of_normal {G : Type*} [Group G] {P E C : Subgroup G}
    (hPE : P ≤ E) (hPn : ∀ e ∈ E, ∀ x ∈ P, e * x * e⁻¹ ∈ P)
    (hEn : ∀ c ∈ C, ∀ e ∈ E, c * e * c⁻¹ ∈ E) : (P.subgroupOf C).IsSubnormal := by
  have hEn' : (E.subgroupOf C).Normal := ⟨fun n hn c => by
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact hEn c c.2 n hn⟩
  refine IsSubnormal.step (P.subgroupOf C) (E.subgroupOf C)
    (fun x hx => mem_subgroupOf.mpr (hPE (mem_subgroupOf.mp hx))) hEn'.isSubnormal
    ⟨fun x hx y => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
  simp only [coe_mul, coe_inv]
  exact hPn _ (mem_subgroupOf.mp y.2) _ hx

theorem isPerfect_sup {G : Type*} [Group G] {A B : Subgroup G} (hA : Group.IsPerfect ↥A)
    (hB : Group.IsPerfect ↥B) : Group.IsPerfect ↥(A ⊔ B) := by
  rw [Subgroup.isPerfect_iff] at hA hB ⊢
  refine le_antisymm (commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  calc A ⊔ B = ⁅A, A⁆ ⊔ ⁅B, B⁆ := by rw [hA, hB]
    _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := sup_le (commutator_mono le_sup_left le_sup_left)
        (commutator_mono le_sup_right le_sup_right)

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

theorem isTwoQuasisimple_spinJ {J : Subgroup (spinGroup (quadOdd 3 K))}
    (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) : IsTwoQuasisimple ↥J := by
  obtain ⟨-, -, -, hO, hq⟩ := spinJ_props hp hp2 hK h5 hJ
  exact ⟨hq.1, LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm hq⟩

theorem isPerfect_spinE : Group.IsPerfect ↥(spinE K) := by
  have h : ∀ J : Subgroup (spinGroup (quadOdd 3 K)),
      (J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) → Group.IsPerfect ↥J := fun J hJ =>
    (spinJ_props hp hp2 hK h5 hJ).2.2.2.2.1
  exact isPerfect_sup (isPerfect_sup (h _ (Or.inl rfl)) (h _ (Or.inr (Or.inl rfl))))
    (h _ (Or.inr (Or.inr rfl)))

theorem conj_mem_spinE {c e : spinGroup (quadOdd 3 K)} (hc : c ∈ centralizer {tSeven K})
    (he : e ∈ spinE K) : c * e * c⁻¹ ∈ spinE K := by
  have hEC := spinE_le_centralizer hp hp2 hK
  have := (normal_spinE hp hp2 hK h5).conj_mem ⟨e, hEC he⟩ (mem_subgroupOf.mpr he) ⟨c, hc⟩
  exact mem_subgroupOf.mp this

theorem conj_mem_spinJ {J : Subgroup (spinGroup (quadOdd 3 K))}
    (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) {e x : spinGroup (quadOdd 3 K)}
    (he : e ∈ spinE K) (hx : x ∈ J) : e * x * e⁻¹ ∈ J := by
  obtain ⟨hJC, hJn, -⟩ := spinJ_props hp hp2 hK h5 hJ
  have hEC := spinE_le_centralizer hp hp2 hK
  have := hJn.conj_mem ⟨x, hJC hx⟩ (mem_subgroupOf.mpr hx) ⟨e, hEC he⟩
  exact mem_subgroupOf.mp this

theorem eq_spinJ_of_normal {P : Subgroup (spinGroup (quadOdd 3 K))} (hPE : P ≤ spinE K)
    (hPn : ∀ e ∈ spinE K, ∀ x ∈ P, e * x * e⁻¹ ∈ P) (hP : IsTwoQuasisimple ↥P) :
    P = spinJ₁ K ∨ P = spinJ₂ K ∨ P = spinJ₃ K := by
  have hEC := spinE_le_centralizer hp hp2 hK
  exact eq_spinJ_of_isTwoComponentIn hp hp2 hK h5 ⟨hPE.trans hEC,
    isSubnormal_subgroupOf_of_normal hPE hPn fun c hc e he => conj_mem_spinE hp hp2 hK h5 hc he,
    hP⟩

end Model

namespace Setup

variable {G : Type} [Group G] [Finite G] (S : Setup G)

abbrev IsJ (J : Subgroup S.X) : Prop := J = spinJ₁ S.K ∨ J = spinJ₂ S.K ∨ J = spinJ₃ S.K

theorem map_le_D {A : Subgroup S.X} (hA : A ≤ centralizer {tSeven S.K}) : A.map S.φ ≤ S.D := by
  rintro _ ⟨x, hx, rfl⟩
  have h := (S.map_centralizer (tSeven S.K)).le ⟨x, hA hx, rfl⟩
  exact ⟨S.hLH (mem_inf.mp h).1, (mem_inf.mp h).2⟩

theorem conj_mem_L_inf_D {d x : G} (hd : d ∈ S.D) (hx : x ∈ S.L ⊓ S.D) :
    d * x * d⁻¹ ∈ S.L ⊓ S.D :=
  mem_inf.mpr ⟨S.hLn d (mem_inf.mp hd).1 x (mem_inf.mp hx).1,
    mul_mem (mul_mem hd (mem_inf.mp hx).2) (inv_mem hd)⟩

theorem odd_relIndex_L_inf_D : Odd ((S.L ⊓ S.D).relIndex S.D) := by
  have hDH : S.D ≤ S.H := inf_le_left
  let L' := S.L.subgroupOf S.H
  let D' := S.D.subgroupOf S.H
  have hL' : L'.Normal := ⟨fun n hn h => by
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact S.hLn h h.2 n hn⟩
  have h1 : L'.relIndex (L' ⊔ D') = L'.relIndex D' := relIndex_sup_left D' L'
  have h2 : L'.relIndex (L' ⊔ D') ∣ L'.index := relIndex_dvd_index_of_le le_sup_left
  have h3 : L'.relIndex D' = S.L.relIndex S.D := relIndex_subgroupOf hDH
  have h4 : (S.L ⊓ S.D).relIndex S.D = S.L.relIndex S.D := inf_relIndex_right S.L S.D
  rw [h4, ← h3, ← h1]
  exact Odd.of_dvd_nat S.hodd h2

theorem le_L_of_isPerfect {P : Subgroup G} (hPD : P ≤ S.D) (hP : Group.IsPerfect ↥P) :
    P ≤ S.L ⊓ S.D :=
  le_of_isPerfect hPD (fun _ hd _ hx => S.conj_mem_L_inf_D hd hx) S.odd_relIndex_L_inf_D hP

theorem spinE_le : spinE S.K ≤ centralizer {tSeven S.K} := spinE_le_centralizer S.hp S.hp2 S.hK

theorem comap_le_centralizer {P : Subgroup G} (hP : P ≤ S.L ⊓ S.D) :
    P.comap S.φ ≤ centralizer {tSeven S.K} ∧ (P.comap S.φ).map S.φ = P := by
  have hPL : P ≤ S.φ.range := S.hrange ▸ hP.trans inf_le_left
  refine ⟨fun x hx => ?_, map_comap_eq_self hPL⟩
  have h : S.φ x ∈ centralizer ({S.t} : Set G) := (mem_inf.mp (mem_inf.mp (hP hx)).2).2
  rw [mem_centralizer_singleton_iff] at h ⊢
  exact S.hφ (by rw [map_mul, map_mul, h])

theorem map_conj_spinE {g : G} (hg : g ∈ normalizer (S.D : Set G)) :
    ((spinE S.K).map S.φ).map (MulAut.conj g).toMonoidHom = (spinE S.K).map S.φ := by
  set E := (spinE S.K).map S.φ
  set Eg := E.map (MulAut.conj g).toMonoidHom
  have hED : E ≤ S.D := S.map_le_D S.spinE_le
  have hEgD : Eg ≤ S.D := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hg x).mp (hED hx)
  have hEperf : Group.IsPerfect ↥E := by
    have := isPerfect_spinE S.hp S.hp2 S.hK S.h5
    exact Group.IsPerfect.map (H := spinE S.K) S.φ
  have hEgperf : Group.IsPerfect ↥Eg := by
    have := hEperf
    exact Group.IsPerfect.map (H := E) (MulAut.conj g).toMonoidHom
  have hEgL := S.le_L_of_isPerfect hEgD hEgperf
  obtain ⟨hPC, hPmap⟩ := S.comap_le_centralizer hEgL
  set P := Eg.comap S.φ
  have hPperf : Group.IsPerfect ↥P := by
    have e : ↥P ≃* ↥Eg :=
      (P.equivMapOfInjective S.φ S.hφ).trans (MulEquiv.subgroupCongr hPmap)
    have := hEgperf
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hPE : P ≤ spinE S.K := le_spinE_of_isPerfect S.hp S.hp2 S.hK S.h5 hPC hPperf
  have hcard : Nat.card P = Nat.card (spinE S.K) := by
    rw [← S.card_map P, hPmap, card_map_of_injective (MulAut.conj g).injective, S.card_map]
  have hPeq : P = spinE S.K := eq_of_le_of_card_ge hPE hcard.ge
  rw [← hPmap, hPeq]

theorem map_conj_J {g : G} (hg : g ∈ normalizer (S.D : Set G)) {J : Subgroup S.X} (hJ : S.IsJ J) :
    ∃ J' : Subgroup S.X, S.IsJ J' ∧
      (J.map S.φ).map (MulAut.conj g).toMonoidHom = J'.map S.φ := by
  obtain ⟨hJC, -, -, -, hJq⟩ := spinJ_props S.hp S.hp2 S.hK S.h5 hJ
  set Jg := (J.map S.φ).map (MulAut.conj g).toMonoidHom
  have hJD : J.map S.φ ≤ S.D := S.map_le_D hJC
  have hJgD : Jg ≤ S.D := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hg x).mp (hJD hx)
  have hJperf : Group.IsPerfect ↥J := hJq.1
  have hJgperf : Group.IsPerfect ↥Jg := by
    have : Group.IsPerfect ↥(J.map S.φ) := Group.IsPerfect.map (H := J) S.φ
    exact Group.IsPerfect.map (H := J.map S.φ) (MulAut.conj g).toMonoidHom
  have hJgL := S.le_L_of_isPerfect hJgD hJgperf
  obtain ⟨hPC, hPmap⟩ := S.comap_le_centralizer hJgL
  set P := Jg.comap S.φ
  have hEg := S.map_conj_spinE hg
  have hJE : J ≤ spinE S.K := by
    rcases hJ with rfl | rfl | rfl
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have hJgE : Jg ≤ (spinE S.K).map S.φ := by
    rw [← hEg]
    exact map_mono (map_mono hJE)
  have hPE : P ≤ spinE S.K := by
    intro x hx
    obtain ⟨e, he, hex⟩ := hJgE hx
    rw [← S.hφ hex]
    exact he
  have hPn : ∀ e ∈ spinE S.K, ∀ x ∈ P, e * x * e⁻¹ ∈ P := by
    intro e he x hx
    have heE : S.φ e ∈ ((spinE S.K).map S.φ).map (MulAut.conj g).toMonoidHom := by
      rw [hEg]
      exact ⟨e, he, rfl⟩
    obtain ⟨_, ⟨e', he', rfl⟩, he'e⟩ := heE
    obtain ⟨_, ⟨j, hj, rfl⟩, hjx⟩ := (hx : S.φ x ∈ Jg)
    change S.φ (e * x * e⁻¹) ∈ Jg
    refine ⟨S.φ (e' * j * e'⁻¹), ⟨_, conj_mem_spinJ S.hp S.hp2 S.hK S.h5 hJ he' hj, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he'e hjx ⊢
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ← he'e, ← hjx]
    group
  have e : ↥J ≃* ↥P := (J.equivMapOfInjective S.φ S.hφ).trans
    (((J.map S.φ).equivMapOfInjective _ (MulAut.conj g).injective).trans
      ((P.equivMapOfInjective S.φ S.hφ).trans (MulEquiv.subgroupCongr hPmap)).symm)
  have hPq : IsTwoQuasisimple ↥P :=
    isTwoQuasisimple_of_mulEquiv e (isTwoQuasisimple_spinJ S.hp S.hp2 S.hK S.h5 hJ)
  exact ⟨P, eq_spinJ_of_normal S.hp S.hp2 S.hK S.h5 hPE hPn hPq, hPmap.symm⟩

theorem eq_of_mem_J {J : Subgroup S.X} (hJ : S.IsJ J) :
    (spinZ S.K ∈ J → J = spinJ₁ S.K) ∧ (tSeven S.K ∈ J → J = spinJ₂ S.K) ∧
      (spinZ S.K * tSeven S.K ∈ J → J = spinJ₃ S.K) := by
  obtain ⟨hzz, hz1, -, htt, ht1, -, hz1J, ht2J, hzt3J, -⟩ := spinZ_facts S.hp S.hp2 S.hK
  have hzt1 : spinZ S.K * tSeven S.K ≠ 1 := by
    intro h
    have := S.facts.2.2.2.2.2.2.1
    apply this
    rw [← S.hφz, ← map_mul, h, map_one]
  have e12 := @eq_one_of_mem_spinJ₁_of_mem_spinJ₂ S.K _ _ S.p S.f S.hp S.hp2 S.hK S.h5
  have e13 := @eq_one_of_mem_spinJ₁_of_mem_spinJ₃ S.K _ _ S.p S.f S.hp S.hp2 S.hK S.h5
  have e23 := @eq_one_of_mem_spinJ₂_of_mem_spinJ₃ S.K _ _ S.p S.f S.hp S.hp2 S.hK S.h5
  rcases hJ with rfl | rfl | rfl
  · exact ⟨fun _ => rfl, fun h => absurd (e12 h ht2J) ht1, fun h => absurd (e13 h hzt3J) hzt1⟩
  · exact ⟨fun h => absurd (e12 hz1J h) hz1, fun _ => rfl, fun h => absurd (e23 h hzt3J) hzt1⟩
  · exact ⟨fun h => absurd (e13 hz1J h) hz1, fun h => absurd (e23 ht2J h) ht1, fun _ => rfl⟩

theorem mem_J : spinZ S.K ∈ spinJ₁ S.K ∧ tSeven S.K ∈ spinJ₂ S.K ∧
    spinZ S.K * tSeven S.K ∈ spinJ₃ S.K := by
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, -⟩ := spinZ_facts S.hp S.hp2 S.hK
  exact ⟨h1, h2, h3⟩

theorem eq_of_map_conj {g : G} {J J' : Subgroup S.X}
    (h : (J.map S.φ).map (MulAut.conj g).toMonoidHom = J'.map S.φ) {x y : S.X} (hx : x ∈ J)
    (hy : g * S.φ x * g⁻¹ = S.φ y) : y ∈ J' := by
  have : S.φ y ∈ J'.map S.φ := by
    rw [← h, ← hy]
    exact ⟨S.φ x, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨y', hy', hyy⟩ := this
  rw [← S.hφ hyy]
  exact hy'

theorem map_conj_J_of_mem_D {d : G} (hd : d ∈ S.D) {J : Subgroup S.X} (hJ : S.IsJ J) :
    (J.map S.φ).map (MulAut.conj d).toMonoidHom = J.map S.φ := by
  obtain ⟨J', hJ', h⟩ := S.map_conj_J (le_normalizer hd) hJ
  have hdz : d * S.z * d⁻¹ = S.z := by
    rw [mem_centralizer_singleton_iff.mp (mem_inf.mp hd).1]
    group
  have hdt : d * S.t * d⁻¹ = S.t := by
    rw [mem_centralizer_singleton_iff.mp (mem_inf.mp hd).2]
    group
  obtain ⟨hz1, ht2, hzt3⟩ := S.mem_J
  obtain ⟨f1, f2, f3⟩ := S.eq_of_mem_J hJ'
  rw [h]
  congr 1
  rcases hJ with rfl | rfl | rfl
  · exact f1 (S.eq_of_map_conj h hz1 (by rw [S.hφz, hdz]))
  · exact f2 (S.eq_of_map_conj h ht2 hdt)
  · refine f3 (S.eq_of_map_conj h hzt3 ?_)
    rw [map_mul, S.hφz]
    calc d * (S.z * S.t) * d⁻¹ = (d * S.z * d⁻¹) * (d * S.t * d⁻¹) := by group
      _ = S.z * S.t := by rw [hdz, hdt]

theorem mem_normalizer_D_of_swap {n : G} (h1 : n * S.t * n⁻¹ = S.z)
    (h2 : n * S.z * n⁻¹ = S.t) : n ∈ normalizer (S.D : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  have key : ∀ a b : G, n * a * n⁻¹ = b → (x * a = a * x ↔
      n * x * n⁻¹ * b = b * (n * x * n⁻¹)) := by
    intro a b hab
    rw [← hab]
    constructor
    · intro h
      calc n * x * n⁻¹ * (n * a * n⁻¹) = n * (x * a) * n⁻¹ := by group
        _ = n * (a * x) * n⁻¹ := by rw [h]
        _ = n * a * n⁻¹ * (n * x * n⁻¹) := by group
    · intro h
      calc x * a = n⁻¹ * (n * x * n⁻¹ * (n * a * n⁻¹)) * n := by group
        _ = n⁻¹ * (n * a * n⁻¹ * (n * x * n⁻¹)) * n := by rw [h]
        _ = a * x := by group
  rw [key S.z S.t h2, key S.t S.z h1]
  exact and_comm

theorem map_conj_swap {n : G} (h1 : n * S.t * n⁻¹ = S.z) (h2 : n * S.z * n⁻¹ = S.t) :
    ((spinJ₁ S.K).map S.φ).map (MulAut.conj n).toMonoidHom = (spinJ₂ S.K).map S.φ ∧
      ((spinJ₂ S.K).map S.φ).map (MulAut.conj n).toMonoidHom = (spinJ₁ S.K).map S.φ ∧
      ((spinJ₃ S.K).map S.φ).map (MulAut.conj n).toMonoidHom = (spinJ₃ S.K).map S.φ := by
  have hn := S.mem_normalizer_D_of_swap h1 h2
  obtain ⟨hz1, ht2, hzt3⟩ := S.mem_J
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨J', hJ', h⟩ := S.map_conj_J hn (Or.inl rfl)
    rw [h, (S.eq_of_mem_J hJ').2.1 (S.eq_of_map_conj h hz1 (by rw [S.hφz, h2]))]
  · obtain ⟨J', hJ', h⟩ := S.map_conj_J hn (Or.inr (Or.inl rfl))
    rw [h, (S.eq_of_mem_J hJ').1 (S.eq_of_map_conj h ht2 (by rw [h1, S.hφz]))]
  · obtain ⟨J', hJ', h⟩ := S.map_conj_J hn (Or.inr (Or.inr rfl))
    refine h.trans ?_
    rw [(S.eq_of_mem_J hJ').2.2 (S.eq_of_map_conj h hzt3 ?_)]
    show n * S.φ (spinZ S.K * tSeven S.K) * n⁻¹ = S.φ (spinZ S.K * tSeven S.K)
    rw [map_mul, S.hφz]
    calc n * (S.z * S.t) * n⁻¹ = (n * S.z * n⁻¹) * (n * S.t * n⁻¹) := by group
      _ = S.t * S.z := by rw [h1, h2]
      _ = S.z * S.t := S.facts.2.2.2.2.1.symm

end Setup

end CFSG.ComponentClassification.HarrisLit.T1.S74
