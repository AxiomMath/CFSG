module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelCopl
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelAxis
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelCost
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelFrame
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelGen

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

omit [Finite K'] [FiniteDimensional K' N] in
private theorem copl_polar_self (x : N) : polar QN x x = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_ne_zero_of_polar {x z : N} (h : polar QN x z = 1) : x ≠ 0 := fun h0 => by
  rw [h0, polar_zero_left] at h
  exact zero_ne_one h

omit [Finite K'] [FiniteDimensional K' N] in
private theorem copl_twist_sing {x g y : N} (hx : QN x = 0) (hg : QN g = 0)
    (hxg : polar QN x g = 1) (hxy : polar QN x y = 0) (hgy : polar QN g y = 0) :
    QN (x + y + QN y • g) = 0 := by
  have hyg : polar QN y g = 0 := by rw [polar_comm]; exact hgy
  rw [QuadraticMap.map_add QN, QuadraticMap.map_add QN, QuadraticMap.map_smul QN, hx, hg,
    polar_smul_right, polar_add_left, hxy, hxg, hyg]
  simp only [zero_add, add_zero, smul_eq_mul, mul_one, mul_zero]
  exact CharTwo.add_self_eq_zero (QN y)

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_twist_pair {x g y : N} (hxg : polar QN x g = 1) (hyg : polar QN y g = 0)
    (hg : QN g = 0) : polar QN (x + y + QN y • g) g = 1 := by
  rw [polar_add_left, polar_add_left, polar_smul_left, hxg, hyg, polar_self_eq_zero hg]
  simp

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_polar_twist {x g y y' : N} (hx : QN x = 0) (hg : QN g = 0)
    (hxg : polar QN x g = 1) (hxy : polar QN x y = 0) (hgy : polar QN g y = 0)
    (hxy' : polar QN x y' = 0) (hgy' : polar QN g y' = 0) :
    polar QN (x + y + QN y • g) (x + y' + QN y' • g) = QN (y + y') := by
  have hgx : polar QN g x = 1 := by rw [polar_comm]; exact hxg
  have hyx : polar QN y x = 0 := by rw [polar_comm]; exact hxy
  have hyg : polar QN y g = 0 := by rw [polar_comm]; exact hgy
  have hy'x : polar QN y' x = 0 := by rw [polar_comm]; exact hxy'
  have hy'g : polar QN y' g = 0 := by rw [polar_comm]; exact hgy'
  rw [QuadraticMap.map_add QN y y']
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
    polar_self_eq_zero hx, polar_self_eq_zero hg, hxg, hgx, hxy', hyx, hyg, hgy',
    smul_eq_mul, mul_zero, mul_one, zero_add, add_zero]
  abel

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_anisotropic {u v : N} (hQu : QN u = 1)
    (hroot : ∀ s : K', s ^ 2 + polar QN u v * s + QN v ≠ 0) {a b : K'} (hab : a ≠ 0 ∨ b ≠ 0) :
    QN (a • u + b • v) ≠ 0 := by
  rw [QuadraticMap.map_add QN, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
    polar_smul_right_eq, hQu]
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := hab.resolve_right (not_not.mpr rfl)
    simpa using ha
  · intro h
    refine hroot (a * b⁻¹) ?_
    have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
    refine (mul_eq_zero.mp ?_).resolve_left hb2
    rw [← h]
    field_simp
    ring

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_comb_mem_perp {P : HypPair QN} {u v : N} (hu : u ∈ P.perp) (hv : v ∈ P.perp)
    (a b : K') : a • u + b • v ∈ P.perp :=
  Submodule.add_mem _ (Submodule.smul_mem _ a hu) (Submodule.smul_mem _ b hv)

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_e_mem_perp {P P' : HypPair QN} (h : P.Orth P') : P'.e ∈ P.perp :=
  HypPair.mem_perp.mpr ⟨h.ee, h.fe⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_f_mem_perp {P P' : HypPair QN} (h : P.Orth P') : P'.f ∈ P.perp :=
  HypPair.mem_perp.mpr ⟨h.ef, h.ff⟩

omit [Finite K'] [FiniteDimensional K' N] in
private theorem copl_correct {z g y : N} (hzg : polar QN z g = 1) (hg : QN g = 0)
    (hyg : polar QN y g = 0) :
    polar QN (y + polar QN y z • g) g = 0 ∧ polar QN (y + polar QN y z • g) z = 0 := by
  have hgz : polar QN g z = 1 := by rw [polar_comm]; exact hzg
  refine ⟨?_, ?_⟩
  · rw [polar_add_left, polar_smul_left, hyg, polar_self_eq_zero hg]
    simp
  · rw [polar_add_left, polar_smul_left, hgz, smul_eq_mul, mul_one]
    exact CharTwo.add_self_eq_zero _

omit [Finite K'] [FiniteDimensional K' N] in
private theorem copl_new {z g y : N} {M : Submodule K' N} (hzM : z ∈ M) (hgM : g ∈ M)
    (hyM : y ∈ M) (hz : QN z = 0) (hg : QN g = 0) (hzg : polar QN z g = 1)
    (hyg : polar QN y g = 0) :
    z + (y + polar QN y z • g) + QN (y + polar QN y z • g) • g ∈ M ∧
      QN (z + (y + polar QN y z • g) + QN (y + polar QN y z • g) • g) = 0 ∧
      polar QN (z + (y + polar QN y z • g) + QN (y + polar QN y z • g) • g) g = 1 := by
  obtain ⟨h1, h2⟩ := copl_correct hzg hg hyg
  have hgz : polar QN g (y + polar QN y z • g) = 0 := by rw [polar_comm]; exact h1
  have hzy : polar QN z (y + polar QN y z • g) = 0 := by rw [polar_comm]; exact h2
  refine ⟨Submodule.add_mem _ (Submodule.add_mem _ hzM (Submodule.add_mem _ hyM
    (Submodule.smul_mem _ _ hgM))) (Submodule.smul_mem _ _ hgM),
    copl_twist_sing hz hg hzg hzy hgz, copl_twist_pair hzg h1 hg⟩

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_mem_of_new {z g y : N} {S : Submodule K' N} (hzS : z ∈ S) (hgS : g ∈ S)
    (hwS : z + (y + polar QN y z • g) + QN (y + polar QN y z • g) • g ∈ S) : y ∈ S := by
  have h : y = (z + (y + polar QN y z • g) + QN (y + polar QN y z • g) • g) - z -
      (polar QN y z + QN (y + polar QN y z • g)) • g := by module
  have h' := Submodule.sub_mem _ (Submodule.sub_mem _ hwS hzS)
    (Submodule.smul_mem _ (polar QN y z + QN (y + polar QN y z • g)) hgS)
  rwa [← h] at h'

omit [Finite K'] [FiniteDimensional K' N] in
private theorem copl_four {e₂ f₂ u v : N} {M : Submodule K' N} (hQe : QN e₂ = 0)
    (hQf : QN f₂ = 0) (hef : polar QN e₂ f₂ = 1) (hue : polar QN e₂ u = 0)
    (huf : polar QN f₂ u = 0) (hve : polar QN e₂ v = 0) (hvf : polar QN f₂ v = 0)
    (he₂ : e₂ ∈ M) (hf₂ : f₂ ∈ M) (hu : u ∈ M) (hv : v ∈ M) (α β : K') :
    ∃ w : ℕ → N, (∀ j < 4, w j ∈ M ∧ QN (w j) = 0 ∧ w j ≠ 0) ∧ polar QN (w 0) (w 1) = 1 ∧
      w 0 = e₂ + (α • u + β • v) + QN (α • u + β • v) • f₂ ∧
      e₂ ∈ Submodule.span K' (w '' Set.Iio 4) ∧ f₂ ∈ Submodule.span K' (w '' Set.Iio 4) ∧
      u ∈ Submodule.span K' (w '' Set.Iio 4) ∧ v ∈ Submodule.span K' (w '' Set.Iio 4) := by
  obtain ⟨d, hd⟩ : ∃ d : N, d = α • u + β • v := ⟨_, rfl⟩
  have hdM : d ∈ M := hd ▸ Submodule.add_mem _ (Submodule.smul_mem _ α hu)
    (Submodule.smul_mem _ β hv)
  have hde : polar QN e₂ d = 0 := by
    rw [hd, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hue, hve]
    simp
  have hdf : polar QN f₂ d = 0 := by
    rw [hd, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, huf, hvf]
    simp
  have hdf' : polar QN d f₂ = 0 := by rw [polar_comm]; exact hdf
  have huf' : polar QN u f₂ = 0 := by rw [polar_comm]; exact huf
  have hvf' : polar QN v f₂ = 0 := by rw [polar_comm]; exact hvf
  obtain ⟨z, hz⟩ : ∃ z : N, z = e₂ + d + QN d • f₂ := ⟨_, rfl⟩
  have hzM : z ∈ M := hz ▸ Submodule.add_mem _ (Submodule.add_mem _ he₂ hdM)
    (Submodule.smul_mem _ _ hf₂)
  have hzQ : QN z = 0 := hz ▸ copl_twist_sing hQe hQf hef hde hdf
  have hzf : polar QN z f₂ = 1 := hz ▸ copl_twist_pair hef hdf' hQf
  obtain ⟨w2, hw2⟩ : ∃ w2 : N,
      w2 = z + (u + polar QN u z • f₂) + QN (u + polar QN u z • f₂) • f₂ := ⟨_, rfl⟩
  obtain ⟨w3, hw3⟩ : ∃ w3 : N,
      w3 = z + (v + polar QN v z • f₂) + QN (v + polar QN v z • f₂) • f₂ := ⟨_, rfl⟩
  obtain ⟨h2M, h2Q, h2f⟩ := hw2 ▸ copl_new hzM hf₂ hu hzQ hQf hzf huf'
  obtain ⟨h3M, h3Q, h3f⟩ := hw3 ▸ copl_new hzM hf₂ hv hzQ hQf hzf hvf'
  obtain ⟨w, hw0, hw1, hw2', hw3'⟩ : ∃ w : ℕ → N, w 0 = z ∧ w 1 = f₂ ∧ w 2 = w2 ∧ w 3 = w3 :=
    ⟨fun j => if j = 0 then z else if j = 1 then f₂ else if j = 2 then w2 else w3,
      by simp, by simp, by simp, by simp⟩
  have hf₂ne : f₂ ≠ 0 := (⟨e₂, f₂, hQe, hQf, hef⟩ : HypPair QN).f_ne_zero
  have hS : ∀ j < 4, w j ∈ Submodule.span K' (w '' Set.Iio 4) := fun j hj =>
    Submodule.subset_span (Set.mem_image_of_mem w (Set.mem_Iio.mpr hj))
  have hzS : z ∈ Submodule.span K' (w '' Set.Iio 4) := hw0 ▸ hS 0 (by norm_num)
  have hf₂S : f₂ ∈ Submodule.span K' (w '' Set.Iio 4) := hw1 ▸ hS 1 (by norm_num)
  have hw2S : w2 ∈ Submodule.span K' (w '' Set.Iio 4) := hw2' ▸ hS 2 (by norm_num)
  have hw3S : w3 ∈ Submodule.span K' (w '' Set.Iio 4) := hw3' ▸ hS 3 (by norm_num)
  have huS : u ∈ Submodule.span K' (w '' Set.Iio 4) := copl_mem_of_new hzS hf₂S (hw2 ▸ hw2S)
  have hvS : v ∈ Submodule.span K' (w '' Set.Iio 4) := copl_mem_of_new hzS hf₂S (hw3 ▸ hw3S)
  have hdS : d ∈ Submodule.span K' (w '' Set.Iio 4) := hd ▸ Submodule.add_mem _
    (Submodule.smul_mem _ α huS) (Submodule.smul_mem _ β hvS)
  refine ⟨w, ?_, ?_, ?_, ?_, hf₂S, huS, hvS⟩
  · intro j hj
    interval_cases j
    · rw [hw0]; exact ⟨hzM, hzQ, copl_ne_zero_of_polar hzf⟩
    · rw [hw1]; exact ⟨hf₂, hQf, hf₂ne⟩
    · rw [hw2']; exact ⟨h2M, h2Q, copl_ne_zero_of_polar h2f⟩
    · rw [hw3']; exact ⟨h3M, h3Q, copl_ne_zero_of_polar h3f⟩
  · rw [hw0, hw1]
    exact hzf
  · rw [hw0, hz, hd]
  · have h : e₂ = z - d - QN d • f₂ := by rw [hz]; module
    have h' := Submodule.sub_mem _ (Submodule.sub_mem _ hzS hdS)
      (Submodule.smul_mem _ (QN d) hf₂S)
    rwa [← h] at h'

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_li_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι] {t g : ι → N}
    (h : ∀ i j, polar QN (t i) (g j) = if i = j then 1 else 0) : LinearIndependent K' t := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have key : ∀ s : Finset ι, polar QN (∑ i ∈ s, c i • t i) (g j) =
      ∑ i ∈ s, c i * polar QN (t i) (g j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, polar_add_left, ih, polar_smul_left,
        smul_eq_mul]
  have h1 : ∑ i, c i * polar QN (t i) (g j) = 0 := by
    rw [← key, hc, polar_zero_left]
  simpa [h] using h1

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_dual_pairs {n : ℕ} (P : Fin n → HypPair QN)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (i j : Fin n × Bool) :
    polar QN (if i.2 then (P i.1).e else (P i.1).f)
      (if j.2 then (P j.1).f else (P j.1).e) = if i = j then 1 else 0 := by
  obtain ⟨a, b⟩ := i
  obtain ⟨c, d⟩ := j
  by_cases hac : a = c
  · subst hac
    cases b <;> cases d <;> simp only [Prod.mk.injEq, and_false,
      Bool.false_eq_true, if_true, if_false, HypPair.polar_ef, HypPair.polar_fe,
      HypPair.polar_ee, HypPair.polar_ff, Bool.true_eq_false]
  · have ho := hP a c hac
    cases b <;> cases d <;> simp only [Prod.mk.injEq, hac, false_and, and_false, if_false,
      ho.ee, ho.ef, ho.fe, ho.ff, Bool.false_eq_true, Bool.true_eq_false, if_true]

omit [Finite K'] [FiniteDimensional K' N] in
private theorem copl_dual {n : ℕ} (P : Fin n → HypPair QN)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) {u v : N}
    (huP : ∀ r, polar QN (P r).e u = 0 ∧ polar QN (P r).f u = 0 ∧
      polar QN (P r).e v = 0 ∧ polar QN (P r).f v = 0) (hpuv : polar QN u v ≠ 0) :
    ∀ i j : (Fin n × Bool) ⊕ Bool,
      polar QN (Sum.elim (fun k : Fin n × Bool => if k.2 then (P k.1).e else (P k.1).f)
        (fun b : Bool => if b then v else u) i)
        (Sum.elim (fun k : Fin n × Bool => if k.2 then (P k.1).f else (P k.1).e)
          (fun b : Bool => if b then (polar QN u v)⁻¹ • u else (polar QN u v)⁻¹ • v) j) =
      if i = j then 1 else 0 := by
  rintro (⟨a, b⟩ | b) (⟨c, d⟩ | d)
  · simpa using copl_dual_pairs P hP (a, b) (c, d)
  · have ha := huP a
    cases b <;> cases d <;> simp [polar_smul_right, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
  · have hc := huP c
    rw [polar_comm]
    cases b <;> cases d <;> simp [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  · cases b <;> cases d
    · show polar QN u ((polar QN u v)⁻¹ • v) =
        if (Sum.inr false : (Fin n × Bool) ⊕ Bool) = Sum.inr false then 1 else 0
      rw [if_pos rfl, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hpuv]
    · show polar QN u ((polar QN u v)⁻¹ • u) =
        if (Sum.inr false : (Fin n × Bool) ⊕ Bool) = Sum.inr true then 1 else 0
      rw [if_neg (by simp), polar_smul_right, copl_polar_self, smul_zero]
    · show polar QN v ((polar QN u v)⁻¹ • v) =
        if (Sum.inr true : (Fin n × Bool) ⊕ Bool) = Sum.inr false then 1 else 0
      rw [if_neg (by simp), polar_smul_right, copl_polar_self, smul_zero]
    · show polar QN v ((polar QN u v)⁻¹ • u) =
        if (Sum.inr true : (Fin n × Bool) ⊕ Bool) = Sum.inr true then 1 else 0
      rw [if_pos rfl, polar_smul_right, polar_comm QN v u, smul_eq_mul, inv_mul_cancel₀ hpuv]

omit [Finite K'] [FiniteDimensional K' N] [CharP K' 2] in
private theorem copl_polar_perp {P : HypPair QN} {y : N} (h : y ∈ P.perp) :
    polar QN y P.e = 0 ∧ polar QN y P.f = 0 :=
  ⟨(polar_comm QN y P.e).trans (HypPair.mem_perp.mp h).1,
    (polar_comm QN y P.f).trans (HypPair.mem_perp.mp h).2⟩

omit [Finite K'] in
private theorem copl_eq_zero_of_perp (hnd : (polarBilin QN).Nondegenerate)
    (hdim : finrank K' N = 8) (P : Fin 3 → HypPair QN) (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    {u v : N} (huv : ∀ i, u ∈ (P i).perp ∧ v ∈ (P i).perp) (hpuv : polar QN u v ≠ 0) {x' : N}
    (hperp : ∀ i, polar QN x' (Sum.elim
      (fun k : Fin 3 × Bool => if k.2 then (P k.1).e else (P k.1).f)
      (fun b : Bool => if b then v else u) i) = 0) : x' = 0 := by
  have huP : ∀ r, polar QN (P r).e u = 0 ∧ polar QN (P r).f u = 0 ∧
      polar QN (P r).e v = 0 ∧ polar QN (P r).f v = 0 := fun r =>
    ⟨(HypPair.mem_perp.mp (huv r).1).1, (HypPair.mem_perp.mp (huv r).1).2,
      (HypPair.mem_perp.mp (huv r).2).1, (HypPair.mem_perp.mp (huv r).2).2⟩
  have hind := copl_li_of_dual (copl_dual P hP huP hpuv)
  have hspan := hind.span_eq_top_of_card_eq_finrank' (by rw [hdim]; simp)
  refine eq_zero_of_polar_eq_zero hnd fun y => ?_
  have hy : y ∈ Submodule.span K' (Set.range (Sum.elim
      (fun k : Fin 3 × Bool => if k.2 then (P k.1).e else (P k.1).f)
      (fun b : Bool => if b then v else u))) := by
    rw [hspan]
    trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hperp i
  | zero => exact polar_zero_right QN x'
  | add y z _ _ hy hz => rw [polar_add_right, hy, hz, add_zero]
  | smul c y _ hy => rw [polar_smul_right, hy, smul_zero]

omit [Finite K'] in
private theorem copl_perp_span (hnd : (polarBilin QN).Nondegenerate) (hdim : finrank K' N = 8)
    (P : Fin 3 → HypPair QN) (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) {u v : N}
    (huv : ∀ i, u ∈ (P i).perp ∧ v ∈ (P i).perp) (hpuv : polar QN u v ≠ 0) {x : N}
    (h0 : x ∈ (P 0).perp) (h1 : x ∈ (P 1).perp) :
    x ∈ Submodule.span K' {(P 2).e, (P 2).f, u, v} := by
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : N, x₂ = (P 2).proj x := ⟨_, rfl⟩
  have hx₂2 : x₂ ∈ (P 2).perp := hx₂ ▸ (P 2).proj_mem_perp x
  have hx₂j : ∀ j : Fin 3, j ≠ 2 → x ∈ (P j).perp → x₂ ∈ (P j).perp := by
    intro j hj hx
    rw [hx₂, HypPair.proj]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hx (Submodule.smul_mem _ _
      (copl_e_mem_perp (hP j 2 (by omega))))) (Submodule.smul_mem _ _
      (copl_f_mem_perp (hP j 2 (by omega))))
  obtain ⟨a, ha⟩ : ∃ a : K', a = (polar QN u v)⁻¹ * polar QN x₂ v := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : K', b = (polar QN u v)⁻¹ * polar QN x₂ u := ⟨_, rfl⟩
  obtain ⟨x', hx'⟩ : ∃ x' : N, x' = x₂ - a • u - b • v := ⟨_, rfl⟩
  have hx'mem : ∀ j : Fin 3, x₂ ∈ (P j).perp → x' ∈ (P j).perp := fun j hj =>
    hx' ▸ Submodule.sub_mem _ (Submodule.sub_mem _ hj (Submodule.smul_mem _ _ (huv j).1))
      (Submodule.smul_mem _ _ (huv j).2)
  have hx'u : polar QN x' u = 0 := by
    rw [hx', polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq,
      copl_polar_self, polar_comm QN v u, hb]
    field_simp
    ring
  have hx'v : polar QN x' v = 0 := by
    rw [hx', polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq,
      copl_polar_self, ha]
    field_simp
    ring
  have hperp : ∀ i, polar QN x' (Sum.elim
      (fun k : Fin 3 × Bool => if k.2 then (P k.1).e else (P k.1).f)
      (fun b : Bool => if b then v else u) i) = 0 := by
    rintro (⟨c, d⟩ | d)
    · have hc : x' ∈ (P c).perp := by
        fin_cases c
        · exact hx'mem 0 (hx₂j 0 (by decide) h0)
        · exact hx'mem 1 (hx₂j 1 (by decide) h1)
        · exact hx'mem 2 hx₂2
      cases d
      · exact (copl_polar_perp hc).2
      · exact (copl_polar_perp hc).1
    · cases d
      · exact hx'u
      · exact hx'v
  have hzero : x' = 0 := copl_eq_zero_of_perp hnd hdim P hP huv hpuv hperp
  have hdec : x = polar QN x (P 2).f • (P 2).e + polar QN x (P 2).e • (P 2).f +
      (a • u + b • v) := by
    have h := (P 2).eq_add_proj x
    rw [← hx₂] at h
    have h' : x₂ = a • u + b • v := by
      rw [hx'] at hzero
      rw [sub_sub, sub_eq_zero] at hzero
      exact hzero
    rw [h'] at h
    exact h
  rw [hdec]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _
    (Submodule.subset_span (by simp))) (Submodule.smul_mem _ _
    (Submodule.subset_span (by simp)))) (Submodule.add_mem _ (Submodule.smul_mem _ _
    (Submodule.subset_span (by simp))) (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))

omit [Finite K'] in
theorem exists_listFrame_minusFour (hnd : (polarBilin QN).Nondegenerate)
    (hdim : finrank K' N = 8) (P : Fin 3 → HypPair QN) (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    {u v : N} (huv : ∀ i, u ∈ (P i).perp ∧ v ∈ (P i).perp) (hQu : QN u = 1)
    (hpuv : polar QN u v ≠ 0) (hroot : ∀ s : K', s ^ 2 + polar QN u v * s + QN v ≠ 0)
    (α β : K') :
    ∃ w : ℕ → N, ∃ j₁ : ℕ, IsListFrame QN (P 0).e (P 0).f (P 1).e (P 1).f w 4 j₁ ∧
      w 0 = (P 2).e + (α • u + β • v) + QN (α • u + β • v) • (P 2).f := by
  have hP01 := hP 0 1 (by decide)
  have hP02 := hP 0 2 (by decide)
  have hP12 := hP 1 2 (by decide)
  obtain ⟨w, hw, hw01, hw0, hSe, hSf, hSu, hSv⟩ := copl_four (M := (P 0).perp ⊓ (P 1).perp)
    (P 2).Q_e (P 2).Q_f (P 2).polar_ef (HypPair.mem_perp.mp (huv 2).1).1
    (HypPair.mem_perp.mp (huv 2).1).2 (HypPair.mem_perp.mp (huv 2).2).1
    (HypPair.mem_perp.mp (huv 2).2).2 ⟨copl_e_mem_perp hP02, copl_e_mem_perp hP12⟩
    ⟨copl_f_mem_perp hP02, copl_f_mem_perp hP12⟩ ⟨(huv 0).1, (huv 1).1⟩ ⟨(huv 0).2, (huv 1).2⟩ α β
  refine ⟨w, 1, ?_, hw0⟩
  exact
    { e_sing := (P 0).Q_e
      f_sing := (P 0).Q_f
      p_sing := (P 1).Q_e
      p'_sing := (P 1).Q_f
      ef := (P 0).polar_ef
      pp' := (P 1).polar_ef
      ep := hP01.ee
      ep' := hP01.ef
      fp := hP01.fe
      fp' := hP01.ff
      w_sing := fun j hj => (hw j hj).2.1
      w_ne := fun j hj => (hw j hj).2.2
      w_e := fun j hj => (HypPair.mem_perp.mp (hw j hj).1.1).1
      w_f := fun j hj => (HypPair.mem_perp.mp (hw j hj).1.1).2
      w_p := fun j hj => (HypPair.mem_perp.mp (hw j hj).1.2).1
      w_p' := fun j hj => (HypPair.mem_perp.mp (hw j hj).1.2).2
      span := fun x h1 h2 h3 h4 => by
        have hx := copl_perp_span hnd hdim P hP huv hpuv (x := x)
          (HypPair.mem_perp.mpr ⟨h1, h2⟩) (HypPair.mem_perp.mpr ⟨h3, h4⟩)
        refine (Submodule.span_le.mpr ?_) hx
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl
        exacts [hSe, hSf, hSu, hSv]
      pos := by norm_num
      j₁_lt := by norm_num
      hyp := hw01 }

private def coplLine (e f p p' : N) (w : ℕ → N) (k j : ℕ) : N × N :=
  if j = 0 then (e, p) else if j ≤ k then (e, w (j - 1)) else if j = k + 1 then (w 0, p)
    else if j = k + 2 then (f, w 0) else if j = k + 3 then (f, p)
    else if j = k + 4 then (f, p') else (0, 0)

private theorem coplLine_zero {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    coplLine e f p p' w k 0 = (e, p) := by
  unfold coplLine
  rw [if_pos rfl]

private theorem coplLine_mid {e f p p' : N} {w : ℕ → N} {k j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    coplLine e f p p' w k j = (e, w (j - 1)) := by
  unfold coplLine
  rw [if_neg (by omega), if_pos h2]

private theorem coplLine_k1 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    coplLine e f p p' w k (k + 1) = (w 0, p) := by
  unfold coplLine
  split_ifs <;> first | rfl | contradiction | omega

private theorem coplLine_k2 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    coplLine e f p p' w k (k + 2) = (f, w 0) := by
  unfold coplLine
  split_ifs <;> first | rfl | contradiction | omega

private theorem coplLine_k3 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    coplLine e f p p' w k (k + 3) = (f, p) := by
  unfold coplLine
  split_ifs <;> first | rfl | contradiction | omega

private theorem coplLine_k4 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    coplLine e f p p' w k (k + 4) = (f, p') := by
  unfold coplLine
  split_ifs <;> first | rfl | contradiction | omega

private theorem coplLine_ge {e f p p' : N} {w : ℕ → N} {k j : ℕ} (h : k + 5 ≤ j) :
    coplLine e f p p' w k j = (0, 0) := by
  unfold coplLine
  split_ifs <;> first | rfl | contradiction | omega

private noncomputable def coplAxis (ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)) (e f p p' : N)
    (w : ℕ → N) (k j : ℕ) : Submodule K V :=
  movedSpace (rhoE ρ (coplLine e f p p' w k j).1 (coplLine e f p p' w k j).2)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem coplAxis_zero {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    coplAxis ρ e f p p' w k 0 = movedSpace (rhoE ρ e p) := by
  unfold coplAxis
  rw [coplLine_zero]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem coplAxis_mid {e f p p' : N} {w : ℕ → N} {k j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) :
    coplAxis ρ e f p p' w k j = movedSpace (rhoE ρ e (w (j - 1))) := by
  unfold coplAxis
  rw [coplLine_mid h1 h2]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem coplAxis_k1 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    coplAxis ρ e f p p' w k (k + 1) = movedSpace (rhoE ρ (w 0) p) := by
  unfold coplAxis
  rw [coplLine_k1]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem coplAxis_k2 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    coplAxis ρ e f p p' w k (k + 2) = movedSpace (rhoE ρ f (w 0)) := by
  unfold coplAxis
  rw [coplLine_k2]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem coplAxis_k3 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    coplAxis ρ e f p p' w k (k + 3) = movedSpace (rhoE ρ f p) := by
  unfold coplAxis
  rw [coplLine_k3]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem coplAxis_k4 {e f p p' : N} {w : ℕ → N} {k : ℕ} :
    coplAxis ρ e f p p' w k (k + 4) = movedSpace (rhoE ρ f p') := by
  unfold coplAxis
  rw [coplLine_k4]

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem copl_movedSpace_one_bot : movedSpace (1 : V ≃ₗ[K] V) = ⊥ := by
  unfold movedSpace
  rw [LinearMap.range_eq_bot]
  ext v
  simp

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem coplAxis_ge {e f p p' : N} {w : ℕ → N} {k j : ℕ} (h : k + 5 ≤ j) :
    coplAxis ρ e f p p' w k j = ⊥ := by
  unfold coplAxis
  rw [coplLine_ge h]
  show movedSpace (rhoE ρ 0 0) = ⊥
  rw [rhoE_zero_right]
  exact copl_movedSpace_one_bot

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem copl_li_e_of {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hs : OmegaSetting QN Qf ρ) (hF : IsListFrame QN e f p p' w k j₁) {x : N} (hx : x ≠ 0)
    (hxf : polar QN f x = 0) : LinearIndependent K' ![e, x] := by
  obtain ⟨z, hz⟩ := exists_polar_ne_zero hs.ndN hx
  refine linearIndependent_pair_of_polar (z₁ := f) (z₂ := z) ?_ ?_ hz
  · rw [hF.ef]; exact one_ne_zero
  · rw [polar_comm QN x f, hxf]

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_li_w0_p {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![w 0, p] :=
  linearIndependent_pair_of_polar (z₁ := w j₁) (z₂ := p') (by rw [hF.hyp]; exact one_ne_zero)
    (hF.w_p j₁ hF.j₁_lt) (by rw [hF.pp']; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_li_w0_f {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![w 0, f] :=
  linearIndependent_pair_of_polar (z₁ := w j₁) (z₂ := e) (by rw [hF.hyp]; exact one_ne_zero)
    (hF.w_f j₁ hF.j₁_lt) (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_li_w0_fp {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![w 0, f + p] :=
  linearIndependent_pair_of_polar (z₁ := w j₁) (z₂ := e) (by rw [hF.hyp]; exact one_ne_zero)
    (by rw [polar_add_left, hF.w_f j₁ hF.j₁_lt, hF.w_p j₁ hF.j₁_lt, add_zero])
    (by
      rw [polar_add_left, polar_comm QN f e, hF.ef, polar_comm QN p e, hF.ep, add_zero]
      exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_li_f_w0 {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![f, w 0] :=
  linearIndependent_pair_of_polar (z₁ := e) (z₂ := w j₁)
    (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)
    (by rw [polar_comm QN (w 0) e, hF.w_e 0 hF.pos]) (by rw [hF.hyp]; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_li_f_p {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![f, p] :=
  linearIndependent_pair_of_polar (z₁ := e) (z₂ := p')
    (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)
    (by rw [polar_comm QN p e, hF.ep]) (by rw [hF.pp']; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_li_f_p' {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![f, p'] :=
  linearIndependent_pair_of_polar (z₁ := e) (z₂ := p)
    (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)
    (by rw [polar_comm QN p' e, hF.ep']) (by rw [polar_comm QN p' p, hF.pp']; exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_li_f_w0p {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![f, w 0 + p] :=
  linearIndependent_pair_of_polar (z₁ := e) (z₂ := p')
    (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)
    (by
      rw [polar_add_left, polar_comm QN (w 0) e, hF.w_e 0 hF.pos, polar_comm QN p e, hF.ep,
        add_zero])
    (by
      rw [polar_add_left, polar_comm QN (w 0) p', hF.w_p' 0 hF.pos, hF.pp', zero_add]
      exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_li_f_w0p' {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) : LinearIndependent K' ![f, w 0 + p'] :=
  linearIndependent_pair_of_polar (z₁ := e) (z₂ := p)
    (by rw [polar_comm QN f e, hF.ef]; exact one_ne_zero)
    (by
      rw [polar_add_left, polar_comm QN (w 0) e, hF.w_e 0 hF.pos, polar_comm QN p' e, hF.ep',
        add_zero])
    (by
      rw [polar_add_left, polar_comm QN (w 0) p, hF.w_p 0 hF.pos, polar_comm QN p' p, hF.pp',
        zero_add]
      exact one_ne_zero)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_li_triple {a d u z : N} (hli : LinearIndependent K' ![a, d])
    (haz : polar QN a z = 0) (hdz : polar QN d z = 0) (huz : polar QN u z ≠ 0) :
    LinearIndependent K' ![a, d, u] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have h2 : g 2 * polar QN u z = 0 := by
    have h := congrArg (fun x => polar QN x z) hg
    simpa [polar_add_left, polar_smul_left_eq, haz, hdz] using h
  have hg2 : g 2 = 0 := (mul_eq_zero.mp h2).resolve_right huz
  rw [hg2, zero_smul, add_zero] at hg
  obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.mp hli (g 0) (g 1) hg
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact hg2

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [CharP K 2] [Finite K]
  [FiniteDimensional K V] in
private theorem coplLine_spec {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hs : OmegaSetting QN Qf ρ) (hF : IsListFrame QN e f p p' w k j₁) {j : ℕ} (hj : j < k + 5) :
    QN (coplLine e f p p' w k j).1 = 0 ∧ QN (coplLine e f p p' w k j).2 = 0 ∧
      polar QN (coplLine e f p p' w k j).1 (coplLine e f p p' w k j).2 = 0 ∧
      LinearIndependent K' ![(coplLine e f p p' w k j).1, (coplLine e f p p' w k j).2] := by
  rcases (show j = 0 ∨ (1 ≤ j ∧ j ≤ k) ∨ j = k + 1 ∨ j = k + 2 ∨ j = k + 3 ∨ j = k + 4 by omega)
    with h | ⟨h1, h2⟩ | h | h | h | h
  · rw [h, coplLine_zero]
    exact ⟨hF.e_sing, hF.p_sing, hF.ep,
      copl_li_e_of hs hF (copl_ne_zero_of_polar hF.pp') hF.fp⟩
  · rw [coplLine_mid h1 h2]
    exact ⟨hF.e_sing, hF.w_sing _ (by omega), hF.w_e _ (by omega),
      copl_li_e_of hs hF (hF.w_ne _ (by omega)) (hF.w_f _ (by omega))⟩
  · rw [h, coplLine_k1]
    exact ⟨hF.w_sing 0 hF.pos, hF.p_sing, (polar_comm QN (w 0) p).trans (hF.w_p 0 hF.pos),
      copl_li_w0_p hF⟩
  · rw [h, coplLine_k2]
    exact ⟨hF.f_sing, hF.w_sing 0 hF.pos, hF.w_f 0 hF.pos, copl_li_f_w0 hF⟩
  · rw [h, coplLine_k3]
    exact ⟨hF.f_sing, hF.p_sing, hF.fp, copl_li_f_p hF⟩
  · rw [h, coplLine_k4]
    exact ⟨hF.f_sing, hF.p'_sing, hF.fp', copl_li_f_p' hF⟩

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem coplLine_wit {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁) {j : ℕ} (hj : j < k + 5) :
    ∃ b c : N, QN b = 0 ∧ QN c = 0 ∧
      polar QN (coplLine e f p p' w k j).1 b = 0 ∧ polar QN (coplLine e f p p' w k j).2 b = 0 ∧
      polar QN (coplLine e f p p' w k j).1 c = 0 ∧ polar QN (coplLine e f p p' w k j).2 c = 0 ∧
      polar QN b c = 1 := by
  rcases (show j = 0 ∨ (1 ≤ j ∧ j ≤ k) ∨ j = k + 1 ∨ j = k + 2 ∨ j = k + 3 ∨ j = k + 4 by omega)
    with h | ⟨h1, h2⟩ | h | h | h | h
  · rw [h, coplLine_zero]
    exact ⟨w 0, w j₁, hF.w_sing 0 hF.pos, hF.w_sing j₁ hF.j₁_lt, hF.w_e 0 hF.pos,
      hF.w_p 0 hF.pos, hF.w_e j₁ hF.j₁_lt, hF.w_p j₁ hF.j₁_lt, hF.hyp⟩
  · rw [coplLine_mid h1 h2]
    exact ⟨p, p', hF.p_sing, hF.p'_sing, hF.ep, (polar_comm QN _ p).trans (hF.w_p _ (by omega)),
      hF.ep', (polar_comm QN _ p').trans (hF.w_p' _ (by omega)), hF.pp'⟩
  · rw [h, coplLine_k1]
    exact ⟨e, f, hF.e_sing, hF.f_sing, (polar_comm QN (w 0) e).trans (hF.w_e 0 hF.pos),
      (polar_comm QN p e).trans hF.ep, (polar_comm QN (w 0) f).trans (hF.w_f 0 hF.pos),
      (polar_comm QN p f).trans hF.fp, hF.ef⟩
  · rw [h, coplLine_k2]
    exact ⟨p, p', hF.p_sing, hF.p'_sing, hF.fp, (polar_comm QN (w 0) p).trans (hF.w_p 0 hF.pos),
      hF.fp', (polar_comm QN (w 0) p').trans (hF.w_p' 0 hF.pos), hF.pp'⟩
  · rw [h, coplLine_k3]
    exact ⟨w 0, w j₁, hF.w_sing 0 hF.pos, hF.w_sing j₁ hF.j₁_lt, hF.w_f 0 hF.pos,
      hF.w_p 0 hF.pos, hF.w_f j₁ hF.j₁_lt, hF.w_p j₁ hF.j₁_lt, hF.hyp⟩
  · rw [h, coplLine_k4]
    exact ⟨w 0, w j₁, hF.w_sing 0 hF.pos, hF.w_sing j₁ hF.j₁_lt, hF.w_f 0 hF.pos,
      hF.w_p' 0 hF.pos, hF.w_f j₁ hF.j₁_lt, hF.w_p' j₁ hF.j₁_lt, hF.hyp⟩

private theorem coplAxis_smul_le (hs : OmegaSetting QN Qf ρ)
    {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hF : IsListFrame QN e f p p' w k j₁) (i : ℕ)
    (μ : K') : movedSpace (rhoE ρ (coplLine e f p p' w k i).1 (μ • (coplLine e f p p' w k i).2)) ≤
      coplAxis ρ e f p p' w k i := by
  by_cases hi : i < k + 5
  · obtain ⟨ha, hd, had, hli⟩ := coplLine_spec hs hF hi
    obtain ⟨b, c, hb, hc, hab, hdb, hac, hdc, hbc⟩ := coplLine_wit hF hi
    unfold coplAxis
    exact hs.movedSpace_rhoE_smul_le ha hd hb hc had hab hdb hac hdc hbc hli μ
  · unfold coplAxis
    rw [coplLine_ge (by omega : k + 5 ≤ i)]
    simp

omit [Finite K'] [Finite K] in
private theorem coplAxis_rank (hs : OmegaSetting QN Qf ρ) {e f p p' : N} {w : ℕ → N}
    {k j₁ : ℕ} (hF : IsListFrame QN e f p p' w k j₁) {j : ℕ} (hj : j < k + 5) :
    finrank K ↥(coplAxis ρ e f p p' w k j) ≤ 2 := by
  obtain ⟨ha, hd, had, hli⟩ := coplLine_spec hs hF hj
  unfold coplAxis
  exact (hs.isLongRootElement_rhoE ha hd had hli).finrank_movedSpace_le_two

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem copl_ov_mid {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hs : OmegaSetting QN Qf ρ) (hF : IsListFrame QN e f p p' w k j₁) {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j ≤ k) : coplAxis ρ e f p p' w k j ⊓ coplAxis ρ e f p p' w k 0 ≠ ⊥ := by
  rw [coplAxis_mid h1 h2, coplAxis_zero]
  have hj : j - 1 < k := by omega
  have hfsum : polar QN f (w (j - 1) + p) = 0 := by
    rw [polar_add_right, hF.w_f _ hj, hF.fp, add_zero]
  have hne : w (j - 1) + p ≠ 0 := by
    refine copl_ne_zero_of_polar (QN := QN) (z := p') ?_
    rw [polar_add_left, (polar_comm QN (w (j - 1)) p').trans (hF.w_p' (j - 1) hj), hF.pp',
      zero_add]
  exact hs.movedSpace_rhoE_inf_ne_bot hF.e_sing (hF.w_sing _ hj) hF.p_sing (hF.w_e _ hj) hF.ep
    ((polar_comm QN _ p).trans (hF.w_p _ hj))
    (copl_li_e_of hs hF (hF.w_ne _ hj) (hF.w_f _ hj))
    (copl_li_e_of hs hF (copl_ne_zero_of_polar hF.pp') hF.fp) (copl_li_e_of hs hF hne hfsum)

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem copl_ov_k2 {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hs : OmegaSetting QN Qf ρ) (hF : IsListFrame QN e f p p' w k j₁) :
    coplAxis ρ e f p p' w k (k + 2) ⊓ coplAxis ρ e f p p' w k (k + 1) ≠ ⊥ := by
  rw [coplAxis_k2, coplAxis_k1, rhoE_comm hF.f_sing (hF.w_sing 0 hF.pos) (hF.w_f 0 hF.pos)]
  exact hs.movedSpace_rhoE_inf_ne_bot (hF.w_sing 0 hF.pos) hF.f_sing hF.p_sing
    ((polar_comm QN (w 0) f).trans (hF.w_f 0 hF.pos))
    ((polar_comm QN (w 0) p).trans (hF.w_p 0 hF.pos)) hF.fp
    (copl_li_w0_f hF) (copl_li_w0_p hF) (copl_li_w0_fp hF)

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem copl_ov_k3 {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hs : OmegaSetting QN Qf ρ) (hF : IsListFrame QN e f p p' w k j₁) :
    coplAxis ρ e f p p' w k (k + 3) ⊓ coplAxis ρ e f p p' w k (k + 2) ≠ ⊥ := by
  rw [coplAxis_k3, coplAxis_k2, inf_comm]
  exact hs.movedSpace_rhoE_inf_ne_bot hF.f_sing (hF.w_sing 0 hF.pos) hF.p_sing
    (hF.w_f 0 hF.pos) hF.fp ((polar_comm QN (w 0) p).trans (hF.w_p 0 hF.pos))
    (copl_li_f_w0 hF) (copl_li_f_p hF) (copl_li_f_w0p hF)

omit [Finite K'] [Finite K] [FiniteDimensional K V] in
private theorem copl_ov_k4 {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hs : OmegaSetting QN Qf ρ) (hF : IsListFrame QN e f p p' w k j₁) :
    coplAxis ρ e f p p' w k (k + 4) ⊓ coplAxis ρ e f p p' w k (k + 2) ≠ ⊥ := by
  rw [coplAxis_k4, coplAxis_k2, inf_comm]
  exact hs.movedSpace_rhoE_inf_ne_bot hF.f_sing (hF.w_sing 0 hF.pos) hF.p'_sing
    (hF.w_f 0 hF.pos) hF.fp' ((polar_comm QN (w 0) p').trans (hF.w_p' 0 hF.pos))
    (copl_li_f_w0 hF) (copl_li_f_p' hF) (copl_li_f_w0p' hF)

private theorem copl_axis_k1_le (hs : OmegaSetting QN Qf ρ) {e f p p' : N} {w : ℕ → N}
    {k j₁ : ℕ} (hF : IsListFrame QN e f p p' w k j₁)
    (hcopl : Copl (planeImage ρ (Submodule.span K' {e, p, w 0}))) :
    coplAxis ρ e f p p' w k (k + 1) ≤
      coplAxis ρ e f p p' w k 0 ⊔ coplAxis ρ e f p p' w k 1 := by
  have hk : 1 ≤ k := hF.pos
  rw [coplAxis_k1, coplAxis_zero, coplAxis_mid (le_refl 1) hk, Nat.sub_self,
    ← rhoE_comm hF.p_sing (hF.w_sing 0 hF.pos) (hF.w_p 0 hF.pos)]
  have hp0 : p ≠ 0 := copl_ne_zero_of_polar hF.pp'
  have hli : LinearIndependent K' ![e, p, w 0] :=
    copl_li_triple (copl_li_e_of hs hF hp0 hF.fp) (hF.w_e j₁ hF.j₁_lt) (hF.w_p j₁ hF.j₁_lt)
      (by rw [hF.hyp]; exact one_ne_zero)
  have hne : movedSpace (rhoE ρ e p) ≠ movedSpace (rhoE ρ e (w 0)) :=
    hs.movedSpace_rhoE_ne hF.e_sing hF.p_sing (hF.w_sing 0 hF.pos) hF.ep (hF.w_e 0 hF.pos) hli
      (fun μ => hs.movedSpace_rhoE_smul_le hF.e_sing hF.p_sing (hF.w_sing 0 hF.pos)
        (hF.w_sing j₁ hF.j₁_lt) hF.ep (hF.w_e 0 hF.pos) (hF.w_p 0 hF.pos)
        (hF.w_e j₁ hF.j₁_lt) (hF.w_p j₁ hF.j₁_lt) hF.hyp (copl_li_e_of hs hF hp0 hF.fp) μ)
      (fun μ => hs.movedSpace_rhoE_smul_le hF.e_sing (hF.w_sing 0 hF.pos) hF.p_sing hF.p'_sing
        (hF.w_e 0 hF.pos) hF.ep ((polar_comm QN (w 0) p).trans (hF.w_p 0 hF.pos)) hF.ep'
        ((polar_comm QN (w 0) p').trans (hF.w_p' 0 hF.pos)) hF.pp'
        (copl_li_e_of hs hF (hF.w_ne 0 hF.pos) (hF.w_f 0 hF.pos)) μ)
  exact hs.movedSpace_rhoE_le_sup_of_copl hF.e_sing hF.p_sing (hF.w_sing 0 hF.pos) hF.ep
    (hF.w_e 0 hF.pos) (hF.w_p 0 hF.pos) hli hcopl hne

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_eichler_mem_span {e : N} {w : ℕ → N} {k : ℕ} {Y : Subgroup (N ≃ₗ[K'] N)}
    (hwe : ∀ j < k, polar QN e (w j) = 0) (hY : ∀ j < k, ∀ c : K', eichler QN e (c • w j) ∈ Y) :
    ∀ x ∈ Submodule.span K' (w '' Set.Iio k),
      polar QN e x = 0 ∧ ∀ c : K', eichler QN e (c • x) ∈ Y := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨hwe j hj, fun c => hY j hj c⟩
  | zero =>
    refine ⟨by rw [polar_zero_right], fun c => ?_⟩
    rw [smul_zero, eichler_zero_right]
    exact Y.one_mem
  | add x y hx hy ihx ihy =>
    have h1 : ∀ c : K', polar QN e (c • x) = 0 := fun c => by
      rw [polar_smul_right_eq, ihx.1, mul_zero]
    have h2 : ∀ c : K', polar QN e (c • y) = 0 := fun c => by
      rw [polar_smul_right_eq, ihy.1, mul_zero]
    refine ⟨by rw [polar_add_right, ihx.1, ihy.1, add_zero], fun c => ?_⟩
    rw [smul_add, ← eichler_mul (h1 c) (h2 c)]
    exact Y.mul_mem (ihx.2 c) (ihy.2 c)
  | smul a x hx ih =>
    refine ⟨by rw [polar_smul_right_eq, ih.1, mul_zero], fun c => ?_⟩
    rw [← mul_smul]
    exact ih.2 (c * a)

omit [CharP K 2] [Finite K] [FiniteDimensional K V] [Finite K'] [FiniteDimensional K' N] in
private theorem copl_generation (hs : OmegaSetting QN Qf ρ)
    {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ} (hF : IsListFrame QN e f p p' w k j₁)
    {Y : Subgroup (N ≃ₗ[K'] N)}
    (hY : ∀ i : ℕ, ∀ c : K',
      eichler QN (coplLine e f p p' w k i).1 (c • (coplLine e f p p' w k i).2) ∈ Y) :
    elementaryGroup QN ≤ Y := by
  have hYl : ∀ j < k, ∀ c : K', eichler QN e (c • w j) ∈ Y := by
    intro j hj c
    have h := hY (j + 1) c
    rwa [coplLine_mid (by omega) (by omega), Nat.add_sub_cancel] at h
  refine elementaryGroup_le_of_frame (fun x hx => eq_zero_of_polar_eq_zero hs.ndN hx)
    hF.e_sing hF.f_sing hF.p_sing hF.p'_sing (hF.w_sing 0 hF.pos) (hF.w_sing j₁ hF.j₁_lt)
    hF.ef hF.pp' hF.hyp hF.ep hF.ep' hF.fp hF.fp' (hF.w_e 0 hF.pos) (hF.w_f 0 hF.pos)
    (hF.w_p 0 hF.pos) (hF.w_p' 0 hF.pos) (hF.w_e j₁ hF.j₁_lt) (hF.w_f j₁ hF.j₁_lt)
    (hF.w_p j₁ hF.j₁_lt) (hF.w_p' j₁ hF.j₁_lt) ?_ ?_ ?_
  · intro x hxe hxf hxp hxp'
    simpa using (copl_eichler_mem_span (fun j hj => hF.w_e j hj) hYl x
      (hF.span x hxe hxf hxp hxp')).2 1
  · intro c
    simpa [coplLine_k3] using hY (k + 3) c
  · intro c
    simpa [coplLine_k4] using hY (k + 4) c

private def coplCost (k j : ℕ) : ℕ :=
  if j = 0 then 2 else if j = k + 1 ∨ k + 5 ≤ j then 0 else 1

omit [CharP K 2] [Finite K] in
private theorem copl_cost_step {A : ℕ → Submodule K V} {k : ℕ}
    (hrank : ∀ j < k + 5, finrank K ↥(A j) ≤ 2) (hbot : ∀ j, k + 5 ≤ j → A j = ⊥)
    (hov : ∀ j, 1 ≤ j → j ≤ k → A j ⊓ A 0 ≠ ⊥) (hcopl : A (k + 1) ≤ A 0 ⊔ A 1)
    (hk : 1 ≤ k) (h₂ : A (k + 2) ⊓ A (k + 1) ≠ ⊥) (h₃ : A (k + 3) ⊓ A (k + 2) ≠ ⊥)
    (h₄ : A (k + 4) ⊓ A (k + 2) ≠ ⊥) (j : ℕ) :
    finrank K ↥(A j ⊔ ⨆ i < j, A i) ≤ finrank K ↥(⨆ i < j, A i) + coplCost k j := by
  have hle : ∀ i n : ℕ, i < n → A i ≤ ⨆ i' < n, A i' := fun i n hi =>
    le_iSup₂ (f := fun i' (_ : i' < n) => A i') i hi
  by_cases hbig : k + 5 ≤ j
  · rw [hbot j hbig, bot_sup_eq]
    exact Nat.le_add_right _ _
  rcases (show j = 0 ∨ (1 ≤ j ∧ j ≤ k) ∨ j = k + 1 ∨ j = k + 2 ∨ j = k + 3 ∨ j = k + 4 by omega)
    with h | ⟨h1, h2⟩ | h | h | h | h
  · subst h
    rw [show coplCost k 0 = 2 by unfold coplCost; rw [if_pos rfl]]
    exact finrank_sup_le_add_two (hrank 0 (by omega))
  · rw [show coplCost k j = 1 by unfold coplCost; rw [if_neg (by omega), if_neg (by omega)]]
    exact finrank_sup_le_add_one (hrank j (by omega)) (hle 0 j (by omega)) (hov j h1 h2)
  · subst h
    rw [show coplCost k (k + 1) = 0 by
      unfold coplCost; rw [if_neg (by omega), if_pos (Or.inl rfl)]]
    exact finrank_sup_le_of_le (hcopl.trans (sup_le (hle 0 (k + 1) (by omega))
      (hle 1 (k + 1) (by omega))))
  · subst h
    rw [show coplCost k (k + 2) = 1 by unfold coplCost; rw [if_neg (by omega), if_neg (by omega)]]
    exact finrank_sup_le_add_one (hrank (k + 2) (by omega)) (hle (k + 1) (k + 2) (by omega)) h₂
  · subst h
    rw [show coplCost k (k + 3) = 1 by unfold coplCost; rw [if_neg (by omega), if_neg (by omega)]]
    exact finrank_sup_le_add_one (hrank (k + 3) (by omega)) (hle (k + 2) (k + 3) (by omega)) h₃
  · subst h
    rw [show coplCost k (k + 4) = 1 by unfold coplCost; rw [if_neg (by omega), if_neg (by omega)]]
    exact finrank_sup_le_add_one (hrank (k + 4) (by omega)) (hle (k + 2) (k + 4) (by omega)) h₄

private theorem sum_coplCost (k : ℕ) : ∑ j ∈ Finset.range (k + 5), coplCost k j = k + 5 := by
  have h1 : ∑ j ∈ Finset.range k, coplCost k (j + 1) = k := by
    rw [Finset.sum_congr rfl (g := fun _ => 1) (fun j hj => ?_)]
    · simp
    · have := Finset.mem_range.mp hj
      unfold coplCost
      rw [if_neg (by omega), if_neg (by omega)]
  have e0 : coplCost k 0 = 2 := by unfold coplCost; rw [if_pos rfl]
  have e1 : coplCost k (k + 1) = 0 := by
    unfold coplCost
    rw [if_neg (by omega), if_pos (Or.inl rfl)]
  have e2 : coplCost k (k + 2) = 1 := by unfold coplCost; rw [if_neg (by omega), if_neg (by omega)]
  have e3 : coplCost k (k + 3) = 1 := by unfold coplCost; rw [if_neg (by omega), if_neg (by omega)]
  have e4 : coplCost k (k + 4) = 1 := by unfold coplCost; rw [if_neg (by omega), if_neg (by omega)]
  rw [show k + 5 = k + 4 + 1 from rfl, Finset.sum_range_succ, e4,
    show k + 4 = k + 3 + 1 from rfl, Finset.sum_range_succ, e3,
    show k + 3 = k + 2 + 1 from rfl, Finset.sum_range_succ, e2,
    show k + 2 = k + 1 + 1 from rfl, Finset.sum_range_succ, e1, Finset.sum_range_succ', h1, e0]

theorem OmegaSetting.finrank_le_of_listFrame_copl (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) {e f p p' : N} {w : ℕ → N} {k j₁ : ℕ}
    (hF : IsListFrame QN e f p p' w k j₁)
    (hcopl : Copl (planeImage ρ (Submodule.span K' {e, p, w 0}))) :
    finrank K V ≤ k + 5 := by
  have hk : 1 ≤ k := hF.pos
  have htopA : (⊤ : Submodule K V) ≤ ⨆ i, coplAxis ρ e f p p' w k i :=
    top_le_iSup_of_generate htop (fun i => (coplLine e f p p' w k i).1)
      (fun i => (coplLine e f p p' w k i).2)
      (copl_generation hs hF (fun i c => Subgroup.subset_closure ⟨i, c, rfl⟩))
      (A := coplAxis ρ e f p p' w k) (fun i c => coplAxis_smul_le hs hF i c)
  have hsup : (⨆ i, coplAxis ρ e f p p' w k i) ≤ ⨆ i < k + 5, coplAxis ρ e f p p' w k i := by
    refine iSup_le fun i => ?_
    by_cases hi : i < k + 5
    · exact le_iSup₂ (f := fun i (_ : i < k + 5) => coplAxis ρ e f p p' w k i) i hi
    · rw [coplAxis_ge (j := i) (by omega)]
      exact bot_le
  have hb : finrank K ↥(⨆ i < k + 5, coplAxis ρ e f p p' w k i) ≤
      ∑ j ∈ Finset.range (k + 5), coplCost k j :=
    finrank_iSup_lt_le_sum (coplAxis ρ e f p p' w k) (coplCost k)
      (fun j => copl_cost_step (A := coplAxis ρ e f p p' w k)
        (fun j hj => coplAxis_rank hs hF hj) (fun _ hj => coplAxis_ge hj)
        (fun _ h1 h2 => copl_ov_mid hs hF h1 h2) (copl_axis_k1_le hs hF hcopl) hk
        (copl_ov_k2 hs hF) (copl_ov_k3 hs hF) (copl_ov_k4 hs hF) j) (k + 5)
  have hmono := Submodule.finrank_mono (htopA.trans hsup)
  rw [finrank_top, sum_coplCost] at *
  omega

theorem OmegaSetting.finrank_le_nine_of_minusFour (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hdim : finrank K' N = 8) (P : Fin 3 → HypPair QN)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) {u v : N}
    (huv : ∀ i, u ∈ (P i).perp ∧ v ∈ (P i).perp) (hQu : QN u = 1) (hpuv : polar QN u v ≠ 0)
    (hroot : ∀ s : K', s ^ 2 + polar QN u v * s + QN v ≠ 0) : finrank K V ≤ 9 := by
  have hP01 := hP 0 1 (by decide)
  have hP02 := hP 0 2 (by decide)
  have hP12 := hP 1 2 (by decide)
  have hli : LinearIndependent K' ![(P 0).e, (P 1).e] :=
    linearIndependent_pair_of_polar (z₁ := (P 0).f) (z₂ := (P 1).f)
      (by rw [(P 0).polar_ef]; exact one_ne_zero)
      (by rw [polar_comm]; exact (hP 0 1 (by decide)).fe)
      (by rw [(P 1).polar_ef]; exact one_ne_zero)
  have hmem : ∀ i : K' × K', (P 2).e + (i.1 • u + i.2 • v) + QN (i.1 • u + i.2 • v) • (P 2).f ∈
      (P 0).perp ⊓ (P 1).perp := by
    intro i
    refine ⟨?_, ?_⟩
    · exact Submodule.add_mem _ (Submodule.add_mem _ (copl_e_mem_perp hP02)
        (copl_comb_mem_perp (huv 0).1 (huv 0).2 _ _))
        (Submodule.smul_mem _ _ (copl_f_mem_perp hP02))
    · exact Submodule.add_mem _ (Submodule.add_mem _ (copl_e_mem_perp hP12)
        (copl_comb_mem_perp (huv 1).1 (huv 1).2 _ _))
        (Submodule.smul_mem _ _ (copl_f_mem_perp hP12))
  have hd2 : ∀ i : K' × K', polar QN (P 2).e (i.1 • u + i.2 • v) = 0 ∧
      polar QN (P 2).f (i.1 • u + i.2 • v) = 0 := fun i =>
    HypPair.mem_perp.mp (copl_comb_mem_perp (huv 2).1 (huv 2).2 i.1 i.2)
  have hzz : ∀ i j : K' × K', i ≠ j →
      polar QN ((P 2).e + (i.1 • u + i.2 • v) + QN (i.1 • u + i.2 • v) • (P 2).f)
        ((P 2).e + (j.1 • u + j.2 • v) + QN (j.1 • u + j.2 • v) • (P 2).f) ≠ 0 := by
    intro i j hij
    rw [copl_polar_twist (P 2).Q_e (P 2).Q_f (P 2).polar_ef (hd2 i).1 (hd2 i).2 (hd2 j).1
      (hd2 j).2]
    have h : (i.1 • u + i.2 • v) + (j.1 • u + j.2 • v) =
        (i.1 + j.1) • u + (i.2 + j.2) • v := by module
    rw [h]
    refine copl_anisotropic hQu hroot ?_
    by_contra hcon
    simp only [not_or, not_not] at hcon
    exact hij (Prod.ext (CharTwo.add_eq_zero.mp hcon.1) (CharTwo.add_eq_zero.mp hcon.2))
  have hcard : Nat.card K + 1 < Nat.card (K' × K') := by
    rw [Nat.card_prod, ← hs.card]
    have h1 : 1 < Nat.card K' := Finite.one_lt_card
    nlinarith
  obtain ⟨i, hi⟩ := hs.exists_copl (a := (P 0).e) (d := (P 1).e) (P 0).Q_e (P 1).Q_e hP01.ee hli
    (fun i : K' × K' => (P 2).e + (i.1 • u + i.2 • v) + QN (i.1 • u + i.2 • v) • (P 2).f)
    (fun i => copl_twist_sing (P 2).Q_e (P 2).Q_f (P 2).polar_ef (hd2 i).1 (hd2 i).2)
    (fun i => (HypPair.mem_perp.mp (hmem i).1).1) (fun i => (HypPair.mem_perp.mp (hmem i).2).1)
    hzz hcard
  obtain ⟨w, j₁, hF, hw0⟩ :=
    exists_listFrame_minusFour hs.ndN hdim P hP huv hQu hpuv hroot i.1 i.2
  have h := hs.finrank_le_of_listFrame_copl htop hF (by rw [hw0]; exact hi)
  omega

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
