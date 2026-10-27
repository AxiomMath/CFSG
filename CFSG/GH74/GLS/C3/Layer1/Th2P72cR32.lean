module

import CFSG.GH74.GLS.C3.Layer1.Th2P72cR20
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma14h
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section L2Outer

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem not_isSolvable_pgl2 {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : L2Field F₀) :
    ¬ Group.IsSolvable (PGL2 F₀) := by
  intro hs
  let e₀ : L2 F₀ ≃* L2 F₀ := MulEquiv.refl _
  have hsimple : IsSimpleGroup (L2 F₀) := Proofs2.isSimpleGroup_of_l2 hF₀ e₀
  have hinj : Function.Injective (MulAut.conj : L2 F₀ →* MulAut (L2 F₀)) := conj_injective_of_L2 e₀
  let ι : L2 F₀ →* PGL2 F₀ :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).comp
      (L2.equivPSL F₀).toMonoidHom
  have hι : Function.Injective ι :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp (L2.equivPSL F₀).injective
  have : Group.IsSolvable (L2 F₀) := Group.isSolvable_of_isSolvable_injective hι
  have hcomm : ∀ a b : L2 F₀, a * b = b * a := (IsSimpleGroup.comm_iff_isSolvable (G := L2 F₀)).2 this
  obtain ⟨a, ha⟩ := exists_ne (1 : L2 F₀)
  apply ha
  apply hinj
  ext b
  simp [hcomm a b]


omit [Finite K] in
theorem exists_conj_fieldAut (e : K ≃* L2 F) (y : MulAut K) (hy : y ^ 2 = 1)
    (hout : y ∉ innDiagSub e) :
    ∃ a : MulAut K, a * y * a⁻¹ = fieldAutHom e (fieldProj e y) ∧ orderOf (fieldProj e y) = 2 := by
  have hσ1 : fieldProj e y ≠ 1 := fun h => hout ((mem_innDiagSub_iff e y).2 h)
  have hy1 : y ≠ 1 := fun h => hσ1 (by rw [h, map_one])
  have hy2 : orderOf y = 2 := orderOf_eq_prime hy hy1
  have hord : orderOf (thetaAut e y) = 2 := by rw [MulEquiv.orderOf_eq]; exact hy2
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr (thetaAut e y) hord hσ1
  refine ⟨(innDiagHom e C)⁻¹, ?_, ?_⟩
  · apply (thetaAut e).injective
    simp only [map_mul, map_inv, thetaAut_innDiagHom, thetaAut_fieldAutHom, inv_inv]
    exact hC
  · have h1 : orderOf (fieldProj e y) ∣ orderOf y := orderOf_map_dvd (fieldProj e) y
    rw [hy2] at h1
    exact ((Nat.dvd_prime Nat.prime_two).1 h1).resolve_left
      (fun h => hσ1 (orderOf_eq_one_iff.1 h))

theorem not_isSolvable_fixed_outer (hF : L2Field F) (hF9 : Nat.card F ≠ 9) (e : K ≃* L2 F)
    (y : MulAut K) (hy : y ^ 2 = 1) (hout : y ∉ innDiagSub e) :
    ¬ Group.IsSolvable ↥(fixedSubgroup K y) := by
  obtain ⟨a, hay, hord⟩ := exists_conj_fieldAut e y hy hout
  intro hs
  have hs' : Group.IsSolvable ↥(fixedSubgroup K (fieldAutHom e (fieldProj e y))) :=
    Group.isSolvable_of_surjective (f := (Proofs2.fixedSubgroupEquivOfConj hay).toMonoidHom)
      (Proofs2.fixedSubgroupEquivOfConj hay).surjective
  obtain ⟨-, -, hpgl⟩ := ivk_1_4a F hF K e (fieldProj e y)
  obtain ⟨F₀, _, _, hq, ⟨ψ⟩⟩ := hpgl (by rw [hord]; exact even_two)
  rw [hord] at hq
  have hq2 : Nat.card F₀ ^ 2 = Nat.card F := hq
  have hFodd : Odd (Nat.card F) := hF.1
  have hF3 : 3 < Nat.card F := hF.2
  have hq0 : 2 ≤ Nat.card F₀ := Finite.one_lt_card
  have hqodd : Odd (Nat.card F₀) := by
    rw [← hq2, sq] at hFodd
    exact (Nat.odd_mul.1 hFodd).1
  have hq3 : 3 < Nat.card F₀ := by
    rcases hqodd with ⟨m, hm⟩
    by_contra hle
    push Not at hle
    have : Nat.card F₀ = 3 := by omega
    apply hF9
    rw [← hq2, this]
    norm_num
  have hF₀ : L2Field F₀ := ⟨hqodd, hq3⟩
  have : Group.IsSolvable (PGL2 F₀) :=
    Group.isSolvable_of_surjective (f := ψ.toMonoidHom) ψ.surjective
  exact not_isSolvable_pgl2 hF₀ this


omit [Finite K] in
theorem centralizer_four_inf_innDiagSub'
    (hF : L2Field F) (e : K ≃* L2 F) (U : Subgroup (MulAut K)) (hUD : U ≤ innDiagSub e)
    (h4 : IsFourSubgroup U) :
    centralizer (U : Set (MulAut K)) ⊓ innDiagSub e = U := by
  have hodd := isOddPrimePower_of_L2Field hF
  obtain ⟨hcomm, -⟩ := isFourSubgroup_props h4
  let ι : ↥(innDiagSub e) ≃* PGL2 F := innDiagEquiv e
  let V : Subgroup (PGL2 F) := (U.subgroupOf (innDiagSub e)).map ι.toMonoidHom
  let ψ : ↥V ≃* ↥U :=
    (Subgroup.equivMapOfInjective (U.subgroupOf (innDiagSub e)) ι.toMonoidHom ι.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hUD)
  have hV : IsKleinFour V :=
    { card_four := (Nat.card_congr ψ.toEquiv).trans h4.2
      exponent_two := (Monoid.exponent_eq_of_mulEquiv ψ).trans (exponent_of_isFourSubgroup h4) }
  have hcent := pgl2_kleinFour_centralizer_eq_self F hodd V hV
  ext g
  constructor
  · rintro ⟨hgC, hgD⟩
    have hmem : ι ⟨g, hgD⟩ ∈ Subgroup.centralizer (V : Set (PGL2 F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hgC (u : MulAut K) hu
    rw [hcent] at hmem
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hmem
    have : u = ⟨g, hgD⟩ := ι.injective hue
    have hu' : (u : MulAut K) ∈ U := hu
    rw [this] at hu'
    exact hu'
  · intro hgU
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, hUD hgU⟩
    intro y hy
    exact hcomm y hy g hgU


theorem dihedral_not_comm {k : ℕ} [NeZero k] (hk : 3 ≤ k) :
    ¬ ∀ a b : DihedralGroup k, a * b = b * a := by
  intro h
  have h1 := h (DihedralGroup.r 1) (DihedralGroup.sr 0)
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h1
  have h2 := DihedralGroup.sr.inj h1
  have h3 : (2 : ZMod k) = 0 := by
    calc (2 : ZMod k) = (0 + 1) - (0 - 1) := by ring
      _ = 0 := by rw [← h2]; ring
  have h4 : k ∣ 2 := (ZMod.natCast_eq_zero_iff 2 k).1 (by exact_mod_cast h3)
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem autZ_L2
    (hF : L2Field F) (hF9 : Nat.card F ≠ 9) (e : K ≃* L2 F) (Eb Pb : Subgroup (MulAut K))
    (hEel : CFSG.IsElementaryAbelian 2 ↥Eb) (hE4 : Nat.card ↥Eb = 4)
    (hsolv : ∀ ε ∈ Eb, ε ≠ 1 → Group.IsSolvable ↥(fixedSubgroup K ε))
    (hdih : ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥Pb ≃* DihedralGroup (2 ^ (n - 1))))
    (hcomm : ∀ p ∈ Pb, ∀ e' ∈ Eb, p * e' = e' * p) : False := by
  obtain ⟨n, hn3, ⟨φ⟩⟩ := hdih
  obtain ⟨hEc, hEsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEel
  have hEinn : Eb ≤ innDiagSub e := by
    intro ε hε
    by_contra hout
    have hε1 : ε ≠ 1 := fun h => hout (h ▸ one_mem _)
    have hε2 : ε ^ 2 = 1 := by rw [sq]; exact hEsq ε hε
    exact not_isSolvable_fixed_outer hF hF9 e ε hε2 hout (hsolv ε hε hε1)
  have hcent := centralizer_four_inf_innDiagSub' hF e Eb hEinn ⟨hEel, hE4⟩
  have hcyc := Proofs2.isCyclic_ringAut_of_L2 hF e
  let ψ : ↥Pb →* (F ≃+* F) := (fieldProj e).comp Pb.subtype
  have hker : ψ.ker ≤ center ↥Pb := by
    intro x hx
    have hx1 : fieldProj e (x : MulAut K) = 1 := hx
    have hxD : (x : MulAut K) ∈ innDiagSub e := (mem_innDiagSub_iff e _).2 hx1
    have hxC : (x : MulAut K) ∈ centralizer (Eb : Set (MulAut K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e' he'
      exact (hcomm x x.2 e' he').symm
    have hxE : (x : MulAut K) ∈ Eb := by
      rw [← hcent]
      exact ⟨hxC, hxD⟩
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    exact hcomm q q.2 x hxE
  have hPcomm : ∀ a b : ↥Pb, a * b = b * a := by
    have := hcyc
    have hPc : IsMulCommutative ↥Pb := ψ.isMulCommutative_of_isCyclic_of_ker_le_center hker
    exact fun a b => mul_comm' a b
  have hk4 : 3 ≤ 2 ^ (n - 1) := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  apply dihedral_not_comm hk4
  intro a b
  apply φ.symm.injective
  rw [map_mul, map_mul]
  exact hPcomm _ _

end L2Outer


section CommClosure

variable {H : Type} [Group H]

theorem closure_comm_normal (g : H) :
    (Subgroup.closure {x : H | ∃ c : H, x = g * c * g⁻¹ * c⁻¹}).Normal := by
  refine ⟨fun x hx d => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, rfl⟩ := hy
    have h1 : d * (g * c * g⁻¹ * c⁻¹) * d⁻¹ = (g * d * g⁻¹ * d⁻¹)⁻¹ * (g * (d * c) * g⁻¹ * (d * c)⁻¹) := by
      group
    rw [h1]
    exact mul_mem (inv_mem (Subgroup.subset_closure ⟨d, rfl⟩))
      (Subgroup.subset_closure ⟨d * c, rfl⟩)
  | one => simp
  | mul a b _ _ iha ihb =>
    have : d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
    rw [this]
    exact mul_mem iha ihb
  | inv a _ iha =>
    have : d * a⁻¹ * d⁻¹ = (d * a * d⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem iha

theorem le_closure_comm_of_simple (g : H) (J : Subgroup H) [J.Normal] (hJ : IsSimpleGroup ↥J)
    (hg : ∃ j ∈ J, g * j ≠ j * g) :
    J ≤ Subgroup.closure {x : H | ∃ c : H, x = g * c * g⁻¹ * c⁻¹} := by
  set M := Subgroup.closure {x : H | ∃ c : H, x = g * c * g⁻¹ * c⁻¹} with hM
  have hMn : M.Normal := closure_comm_normal g
  have hN : (M.subgroupOf J).Normal := Subgroup.Normal.subgroupOf hMn J
  rcases hJ.eq_bot_or_eq_top_of_normal (M.subgroupOf J) with hbot | htop
  · exfalso
    obtain ⟨j, hj, hgj⟩ := hg
    have hmem : g * j * g⁻¹ * j⁻¹ ∈ M := Subgroup.subset_closure ⟨j, rfl⟩
    have hJm : g * j * g⁻¹ * j⁻¹ ∈ J :=
      J.mul_mem (Subgroup.Normal.conj_mem inferInstance j hj g) (J.inv_mem hj)
    have h1 : (⟨g * j * g⁻¹ * j⁻¹, hJm⟩ : ↥J) ∈ M.subgroupOf J := hmem
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : g * j * g⁻¹ * j⁻¹ = 1 := congrArg Subtype.val h1
    apply hgj
    calc g * j = (g * j * g⁻¹ * j⁻¹) * j * g := by group
      _ = j * g := by rw [h2]; group
  · intro x hx
    have : (⟨x, hx⟩ : ↥J) ∈ M.subgroupOf J := by rw [htop]; exact Subgroup.mem_top _
    exact this

end CommClosure

section Core

variable {F₀ K₀ : Type} [Field F₀] [Finite F₀] [Group K₀] [Finite K₀]

omit [Finite K₀] in
theorem innAut_normal_aux (k : K₀) (a : MulAut K₀) : a * MulAut.conj k * a⁻¹ = MulAut.conj (a k) := by
  ext x
  simp [MulAut.conj_apply]

omit [Finite K₀] in
theorem innAut_conj_mem (a : MulAut K₀) {x : MulAut K₀} (hx : x ∈ innAut K₀) :
    a * x * a⁻¹ ∈ innAut K₀ := by
  obtain ⟨k, rfl⟩ := hx
  rw [innAut_normal_aux]
  exact ⟨a k, rfl⟩

theorem exists_involution_cent_comm (hF₀ : L2Field F₀) (e₀ : K₀ ≃* L2 F₀) (v : MulAut K₀)
    (hv : v ∈ innDiagSub e₀) (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    ∃ w : K₀, w * w = 1 ∧ w ≠ 1 ∧ v w = w ∧ MulAut.conj w ≠ v ∧
      MulAut.conj w ∈ Subgroup.closure {x : MulAut K₀ | ∃ c ∈ innDiagSub e₀, x = v * c * v⁻¹ * c⁻¹} := by
  classical
  have hord : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  have hinj : Function.Injective (MulAut.conj : K₀ →* MulAut K₀) := conj_injective_of_L2 e₀
  obtain ⟨k, hk2, ⟨φ⟩⟩ := exists_dihedral_fixed hF₀ e₀ v hv hord
  have : NeZero k := ⟨by omega⟩
  have hsr : ∀ j : ZMod k, ((φ.symm (DihedralGroup.sr j)).1 : K₀) * (φ.symm (DihedralGroup.sr j)).1 = 1 ∧
      (φ.symm (DihedralGroup.sr j)).1 ≠ 1 ∧ v (φ.symm (DihedralGroup.sr j)).1 = (φ.symm (DihedralGroup.sr j)).1 := by
    intro j
    refine ⟨?_, ?_, (φ.symm (DihedralGroup.sr j)).2⟩
    · have : φ.symm (DihedralGroup.sr j) * φ.symm (DihedralGroup.sr j) = 1 := by
        rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
      exact congrArg Subtype.val this
    · intro h
      have h1 : φ.symm (DihedralGroup.sr j) = 1 := Subtype.ext (by simpa using h)
      have h2 : DihedralGroup.sr j = 1 := by
        rw [← map_one φ.symm] at h1
        exact φ.symm.injective h1
      rw [DihedralGroup.one_def] at h2
      cases h2
  have hne : (φ.symm (DihedralGroup.sr (0 : ZMod k))).1 ≠ (φ.symm (DihedralGroup.sr (1 : ZMod k))).1 := by
    intro h
    have h1 : φ.symm (DihedralGroup.sr (0 : ZMod k)) = φ.symm (DihedralGroup.sr (1 : ZMod k)) :=
      Subtype.ext h
    have h2 := DihedralGroup.sr.inj (φ.symm.injective h1)
    have h3 : (1 : ZMod k) = 0 := h2.symm
    have h4 : k ∣ 1 := (ZMod.natCast_eq_zero_iff 1 k).1 (by exact_mod_cast h3)
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  obtain ⟨w, hww, hw1, hvw, hcw⟩ : ∃ w : K₀, w * w = 1 ∧ w ≠ 1 ∧ v w = w ∧ MulAut.conj w ≠ v := by
    by_cases h1 : MulAut.conj (φ.symm (DihedralGroup.sr (0 : ZMod k))).1 = v
    · refine ⟨(φ.symm (DihedralGroup.sr (1 : ZMod k))).1, (hsr 1).1, (hsr 1).2.1, (hsr 1).2.2, ?_⟩
      intro h2
      exact hne (hinj (h1.trans h2.symm))
    · exact ⟨_, (hsr 0).1, (hsr 0).2.1, (hsr 0).2.2, h1⟩
  refine ⟨w, hww, hw1, hvw, hcw, ?_⟩
  have hIH : innAut K₀ ≤ innDiagSub e₀ := innAut_le_innDiagSub e₀
  let J : Subgroup ↥(innDiagSub e₀) := (innAut K₀).subgroupOf (innDiagSub e₀)
  have hJn : J.Normal := by
    refine ⟨fun x hx d => ?_⟩
    exact innAut_conj_mem (d : MulAut K₀) hx
  have hJs : IsSimpleGroup ↥J := by
    let e1 : ↥J ≃* ↥(innAut K₀) := Subgroup.subgroupOfEquivOfLe hIH
    let e2 : K₀ ≃* ↥(innAut K₀) := MonoidHom.ofInjective hinj
    have hsimple : IsSimpleGroup K₀ := (Proofs2.isSimpleGroup_of_l2 hF₀ e₀)
    exact (e1.trans e2.symm).isSimpleGroup_congr.2 hsimple
  have hg : ∃ j ∈ J, (⟨v, hv⟩ : ↥(innDiagSub e₀)) * j ≠ j * ⟨v, hv⟩ := by
    by_contra hno
    push Not at hno
    apply hv1
    ext k
    have h1 := hno ⟨MulAut.conj k, hIH ⟨k, rfl⟩⟩ ⟨k, rfl⟩
    have h2 : v * MulAut.conj k = MulAut.conj k * v := congrArg Subtype.val h1
    have h3 : MulAut.conj (v k) = MulAut.conj k := by
      rw [← innAut_normal_aux, h2]
      group
    exact hinj h3
  have hle := le_closure_comm_of_simple (⟨v, hv⟩ : ↥(innDiagSub e₀)) J hJs hg
  have hwJ : (⟨MulAut.conj w, hIH ⟨w, rfl⟩⟩ : ↥(innDiagSub e₀)) ∈ J := ⟨w, rfl⟩
  have hmem := hle hwJ
  have hmap := Subgroup.mem_map_of_mem (innDiagSub e₀).subtype hmem
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨x, ⟨c, rfl⟩, rfl⟩
  exact ⟨c, c.2, by simp⟩

end Core

section FieldCase

variable {F K : Type} [Field F] [Finite F] [Group K] [Finite K]

omit [Finite K] in
theorem autU_L2_field (hF : L2Field F) (e : K ≃* L2 F) (s : F ≃+* F) (hs : orderOf s = 2)
    (hq : 3 < Nat.card (fixedField s)) (A : MulAut K) (hA : A ∈ innDiagSub e) (hA2 : A * A = 1)
    (hA1 : A ≠ 1) (hAf : A * fieldAutHom e s = fieldAutHom e s * A) :
    ∃ u : K, u * u = 1 ∧ u ≠ 1 ∧ fieldAutHom e s u = u ∧ A u = u ∧
      u ∈ Subgroup.closure {x : K | ∃ c ∈ fixedSubgroup K (fieldAutHom e s), x = A c * c⁻¹} ∧
      MulAut.conj u ≠ A := by
  classical
  set f : MulAut K := fieldAutHom e s with hf
  have heven : Even (orderOf s) := by rw [hs]; exact even_two
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_L2 e
  set C : Subgroup K := fixedSubgroup K f with hC
  have hcard := fixedField_card_pow s
  rw [hs] at hcard
  have hF₀ : L2Field (fixedField s) := by
    refine ⟨?_, hq⟩
    have hodd : Odd (Nat.card (fixedField s) ^ 2) := by rw [hcard]; exact hF.1
    rw [sq] at hodd
    exact (Nat.odd_mul.1 hodd).1
  let e₀ : L2 (fixedField s) ≃* L2 (fixedField s) := MulEquiv.refl _
  have hinj₀ : Function.Injective (MulAut.conj : L2 (fixedField s) →* MulAut (L2 (fixedField s))) :=
    conj_injective_of_L2 e₀
  let ψ : ↥C ≃* PGL2 (fixedField s) := fixedSubgroupEquivPGL2 e s heven
  let Φ' : ↥C ≃* ↥(innDiagSub e₀) := ψ.trans (innDiagEquiv e₀).symm
  let Φ : ↥C →* MulAut (L2 (fixedField s)) := (innDiagSub e₀).subtype.comp Φ'.toMonoidHom
  have hΦ : Function.Injective Φ := (Subgroup.subtype_injective _).comp Φ'.injective
  have hAmem : A ∈ centralizer ({f} : Set (MulAut K)) ⊓ innDiagSub e :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 hAf, hA⟩
  rw [← map_conj_fixedSubgroup_of_even e s heven] at hAmem
  obtain ⟨a₀, ha₀C, ha₀⟩ := hAmem
  have hAa : ∀ x : K, A x = a₀ * x * a₀⁻¹ := by
    intro x
    rw [← ha₀]
    simp [MulAut.conj_apply]
  set a₀' : ↥C := ⟨a₀, ha₀C⟩ with ha₀'
  have ha₀2 : a₀ * a₀ = 1 := by
    apply hinj
    rw [map_mul, ha₀, hA2, map_one]
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    apply hA1
    rw [← ha₀, h, map_one]
  set v : MulAut (L2 (fixedField s)) := Φ a₀' with hv
  have hvH : v ∈ innDiagSub e₀ := (Φ' a₀').2
  have hv2 : v * v = 1 := by
    rw [hv, ← map_mul]
    have : a₀' * a₀' = 1 := Subtype.ext ha₀2
    rw [this, map_one]
  have hv1 : v ≠ 1 := by
    intro h
    apply ha₀1
    have : a₀' = 1 := hΦ (by rw [← hv, h, map_one])
    exact congrArg Subtype.val this
  obtain ⟨w, hww, hw1, hvw, hcw, hwcl⟩ := exists_involution_cent_comm hF₀ e₀ v hvH hv2 hv1
  have hconjH : MulAut.conj w ∈ innDiagSub e₀ := innAut_le_innDiagSub e₀ ⟨w, rfl⟩
  set u' : ↥C := Φ'.symm ⟨MulAut.conj w, hconjH⟩ with hu'
  have hΦu' : Φ u' = MulAut.conj w := by
    show ((Φ' (Φ'.symm ⟨MulAut.conj w, hconjH⟩) : ↥(innDiagSub e₀)) : MulAut (L2 (fixedField s))) = _
    rw [MulEquiv.apply_symm_apply]
  refine ⟨u'.1, ?_, ?_, u'.2, ?_, ?_, ?_⟩
  · have : u' * u' = 1 := by
      apply hΦ
      rw [map_mul, hΦu', ← map_mul, hww, map_one, map_one]
    exact congrArg Subtype.val this
  · intro h
    have : u' = 1 := Subtype.ext h
    have h2 : MulAut.conj w = 1 := by rw [← hΦu', this, map_one]
    exact hw1 (hinj₀ (h2.trans (map_one _).symm))
  ·
    rw [hAa]
    have : a₀' * u' * a₀'⁻¹ = u' := by
      apply hΦ
      rw [map_mul, map_mul, map_inv, hΦu', ← hv, innAut_normal_aux, hvw]
    exact congrArg Subtype.val this
  · have hΦsymm : ∀ (c' : MulAut (L2 (fixedField s))) (hc' : c' ∈ innDiagSub e₀),
        Φ (Φ'.symm ⟨c', hc'⟩) = c' := by
      intro c' hc'
      show ((Φ' (Φ'.symm ⟨c', hc'⟩) : ↥(innDiagSub e₀)) : MulAut (L2 (fixedField s))) = _
      rw [MulEquiv.apply_symm_apply]
    set S_C : Set ↥C := {x | ∃ c : ↥C, x = a₀' * c * a₀'⁻¹ * c⁻¹} with hS_C
    have hu'M : u' ∈ Subgroup.closure S_C := by
      have h1 : Subgroup.closure {x : MulAut (L2 (fixedField s)) |
          ∃ c ∈ innDiagSub e₀, x = v * c * v⁻¹ * c⁻¹} ≤ (Subgroup.closure S_C).map Φ := by
        rw [Subgroup.closure_le]
        rintro _ ⟨c', hc', rfl⟩
        refine ⟨a₀' * Φ'.symm ⟨c', hc'⟩ * a₀'⁻¹ * (Φ'.symm ⟨c', hc'⟩)⁻¹,
          Subgroup.subset_closure ⟨_, rfl⟩, ?_⟩
        simp only [map_mul, map_inv, hΦsymm]
        rfl
      have h2 := h1 hwcl
      rw [← hΦu'] at h2
      obtain ⟨x, hx, hxu⟩ := h2
      have hxu' : x = u' := hΦ hxu
      rw [hxu'] at hx
      exact hx
    have h3 := Subgroup.mem_map_of_mem C.subtype hu'M
    rw [MonoidHom.map_closure] at h3
    refine Subgroup.closure_mono ?_ h3
    rintro _ ⟨x, ⟨c, rfl⟩, rfl⟩
    refine ⟨c.1, c.2, ?_⟩
    simp [hAa, ha₀']
  · intro h
    apply hcw
    have h1 : u'.1 = a₀ := hinj (h.trans ha₀.symm)
    have : u' = a₀' := Subtype.ext h1
    rw [← hΦu', this]

end FieldCase

section U2Aux

variable {F K : Type} [Field F] [Finite F] [Group K]

theorem eq_of_orderOf_two_cyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have h2 : 2 ∣ Fintype.card G := by
    rw [← Nat.card_eq_fintype_card]
    exact hx ▸ orderOf_dvd_natCard x
  have hcard := IsCyclic.card_orderOf_eq_totient h2
  have hone : (Finset.univ.filter fun a : G => orderOf a = 2).card = 1 := by
    rw [hcard]
    decide
  obtain ⟨z, hz⟩ := Finset.card_eq_one.1 hone
  have hxz : x ∈ ({z} : Finset G) := by
    rw [← hz]
    simp [hx]
  have hyz : y ∈ ({z} : Finset G) := by
    rw [← hz]
    simp [hy]
  rw [Finset.mem_singleton] at hxz hyz
  rw [hxz, hyz]

theorem closure_aut_comm_normal (σ : MulAut K) :
    (Subgroup.closure {x : K | ∃ c : K, x = σ c * c⁻¹}).Normal := by
  refine ⟨fun x hx d => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, rfl⟩ := hy
    have h1 : d * (σ c * c⁻¹) * d⁻¹ = (σ d * d⁻¹)⁻¹ * (σ (d * c) * (d * c)⁻¹) := by
      simp only [map_mul, mul_inv_rev]
      group
    rw [h1]
    exact mul_mem (inv_mem (Subgroup.subset_closure ⟨d, rfl⟩))
      (Subgroup.subset_closure ⟨d * c, rfl⟩)
  | one => simp
  | mul a b _ _ iha ihb =>
    have : d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
    rw [this]
    exact mul_mem iha ihb
  | inv a _ iha =>
    have : d * a⁻¹ * d⁻¹ = (d * a * d⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem iha

theorem closure_aut_comm_eq_top [IsSimpleGroup K] (σ : MulAut K) (hσ : σ ≠ 1) :
    Subgroup.closure {x : K | ∃ c : K, x = σ c * c⁻¹} = ⊤ := by
  have hn := closure_aut_comm_normal σ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.closure {x : K | ∃ c : K, x = σ c * c⁻¹}) with h | h
  · exfalso
    apply hσ
    ext c
    have : σ c * c⁻¹ ∈ Subgroup.closure {x : K | ∃ c : K, x = σ c * c⁻¹} :=
      Subgroup.subset_closure ⟨c, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact mul_inv_eq_one.1 this
  · exact h

end U2Aux




section U2Main

variable {F K : Type} [Field F] [Finite F] [Group K] [Finite K]

theorem exists_involution_fixed_outer (e : K ≃* L2 F) (y : MulAut K) (hy : y ^ 2 = 1)
    (hout : y ∉ innDiagSub e) : ∃ u : K, u * u = 1 ∧ u ≠ 1 ∧ y u = u := by
  obtain ⟨a, hay, hord⟩ := exists_conj_fieldAut e y hy hout
  set s := fieldProj e y with hs
  have heven : Even (orderOf s) := by rw [hord]; exact even_two
  let ψ : ↥(fixedSubgroup K y) ≃* PGL2 (fixedField s) :=
    (Proofs2.fixedSubgroupEquivOfConj hay).trans (fixedSubgroupEquivPGL2 e s heven)
  have h2 : 2 ∣ Nat.card (PGL2 (fixedField s)) := by
    rw [pgl2_card_formula]
    rcases Nat.even_or_odd (Nat.card (fixedField s)) with h | h
    · exact (h.mul_right _).two_dvd
    · have h1 : Odd (Nat.card (fixedField s) ^ 2) := h.pow
      have h3 : 1 ≤ Nat.card (fixedField s) ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
      exact (Nat.Odd.sub_odd h1 odd_one |>.mul_left _).two_dvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (PGL2 (fixedField s)) := Finite.of_equiv _ ψ.toEquiv
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  let z : ↥(fixedSubgroup K y) := ψ.symm x
  have hz2 : orderOf z = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hx
  refine ⟨z.1, ?_, ?_, z.2⟩
  · have : z * z = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one z
      rwa [hz2] at this
    exact congrArg Subtype.val this
  · intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz2
    omega

end U2Main


theorem isSolvable_dihedral' (z : ℕ) [NeZero z] : Group.IsSolvable (DihedralGroup z) := by
  classical
  let R : Subgroup (DihedralGroup z) := Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup z)
  have hRnormal : R.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simp [DihedralGroup.r_mul_r]
    · refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
      simp [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.inv_sr]
  have : IsCyclic R := Subgroup.isCyclic_zpowers _
  let : CommGroup R := IsCyclic.commGroup
  have hRcard : Nat.card R = z := by rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have hQcard : Nat.card (DihedralGroup z ⧸ R) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup R
    rw [DihedralGroup.nat_card, hRcard] at h
    have hz : 0 < z := Nat.pos_of_ne_zero (NeZero.ne z)
    exact (Nat.eq_of_mul_eq_mul_right hz h).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (DihedralGroup z ⧸ R) := isCyclic_of_prime_card hQcard
  let : CommGroup (DihedralGroup z ⧸ R) := IsCyclic.commGroup
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])


section U2Final

variable {F K : Type} [Field F] [Finite F] [Group K] [Finite K]

theorem autU_L2 (hF : L2Field F)
    (e : K ≃* L2 F) (ε σ : MulAut K) (hε2 : ε ^ 2 = 1) (hσ2 : σ ^ 2 = 1) (hεσ : ε * σ = σ * ε)
    (hσ1 : σ ≠ 1) (hσε : σ ≠ ε) (hns : ¬ Group.IsSolvable ↥(fixedSubgroup K ε)) :
    ∃ u : K, u ^ 2 = 1 ∧ u ≠ 1 ∧ ε u = u ∧ σ u = u ∧
      u ∈ Subgroup.closure {x : K | ∃ c ∈ fixedSubgroup K ε, x = σ c * c⁻¹} ∧
      MulAut.conj u ∉ ({1, ε, σ, ε * σ} : Set (MulAut K)) := by
  classical
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_L2 e
  have hsimple : IsSimpleGroup K := Proofs2.isSimpleGroup_of_l2 hF e
  have hσ2' : σ * σ = 1 := by rw [← sq]; exact hσ2
  have hε2' : ε * ε = 1 := by rw [← sq]; exact hε2
  by_cases hε1 : ε = 1
  ·
    subst hε1
    have hfix : fixedSubgroup K (1 : MulAut K) = ⊤ := by
      ext k
      simp [fixedSubgroup]
    obtain ⟨u, hu2, hu1, hσu, hcu⟩ :
        ∃ u : K, u * u = 1 ∧ u ≠ 1 ∧ σ u = u ∧ MulAut.conj u ≠ σ := by
      by_cases hσD : σ ∈ innDiagSub e
      · obtain ⟨w, hw2, hw1, hσw, hcw, -⟩ := exists_involution_cent_comm hF e σ hσD hσ2' hσ1
        exact ⟨w, hw2, hw1, hσw, hcw⟩
      · obtain ⟨u, hu2, hu1, hσu⟩ := exists_involution_fixed_outer e σ hσ2 hσD
        refine ⟨u, hu2, hu1, hσu, ?_⟩
        intro h
        exact hσD (h ▸ innAut_le_innDiagSub e ⟨u, rfl⟩)
    refine ⟨u, by rw [sq]; exact hu2, hu1, rfl, hσu, ?_, ?_⟩
    · have hM := closure_aut_comm_eq_top σ hσ1
      have : u ∈ Subgroup.closure {x : K | ∃ c : K, x = σ c * c⁻¹} := by
        rw [hM]
        trivial
      refine Subgroup.closure_mono ?_ this
      rintro _ ⟨c, rfl⟩
      exact ⟨c, by rw [hfix]; trivial, rfl⟩
    · intro hmem
      rcases hmem with h | h | h | h
      · exact hu1 (hinj (h.trans (map_one _).symm))
      · exact hu1 (hinj (h.trans (map_one _).symm))
      · exact hcu h
      · exact hcu (h.trans (one_mul σ))
  · by_cases hεD : ε ∈ innDiagSub e
    · exfalso
      apply hns
      have hord : orderOf ε = 2 := orderOf_eq_prime hε2 hε1
      obtain ⟨k, hk2, ⟨φ⟩⟩ := exists_dihedral_fixed hF e ε hεD hord
      have : NeZero k := ⟨by omega⟩
      have := isSolvable_dihedral' k
      exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    ·
      obtain ⟨a, haε, hord⟩ := exists_conj_fieldAut e ε hε2 hεD
      set s := fieldProj e ε with hs
      set f := fieldAutHom e s with hf
      have hss : s * s = 1 := by
        rw [← sq]
        have := pow_orderOf_eq_one s
        rwa [hord] at this
      have hff : f * f = 1 := by rw [hf, ← map_mul, hss, map_one]
      have hfD : f ∉ innDiagSub e := by
        intro h
        have h1 : fieldProj e f = 1 := (mem_innDiagSub_iff e f).1 h
        rw [hf, fieldProj_fieldAutHom] at h1
        rw [h1, orderOf_one] at hord
        omega
      have hfD' : ∀ x : MulAut K, x ∈ innDiagSub e → x * f ∉ innDiagSub e ∧ f * x ∉ innDiagSub e := by
        intro x hx
        constructor
        · intro h
          apply hfD
          have : f = x⁻¹ * (x * f) := by group
          rw [this]
          exact mul_mem (inv_mem hx) h
        · intro h
          apply hfD
          have : f = (f * x) * x⁻¹ := by group
          rw [this]
          exact mul_mem h (inv_mem hx)
      have hεa : ε * a⁻¹ = a⁻¹ * f := by
        calc ε * a⁻¹ = a⁻¹ * (a * ε * a⁻¹) := by group
          _ = a⁻¹ * f := by rw [haε]
      have hεa' : ∀ x : K, ε (a⁻¹ x) = a⁻¹ (f x) := fun x => by
        have := congrArg (fun m : MulAut K => m x) hεa
        simpa using this
      obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : MulAut K, σ₁ = a * σ * a⁻¹ := ⟨_, rfl⟩
      have hσa : σ * a⁻¹ = a⁻¹ * σ₁ := by
        rw [hσ₁]
        group
      have hσa' : ∀ x : K, σ (a⁻¹ x) = a⁻¹ (σ₁ x) := fun x => by
        have := congrArg (fun m : MulAut K => m x) hσa
        simpa using this
      have hσ₁f : σ₁ * f = f * σ₁ := by
        rw [hσ₁, ← haε]
        calc a * σ * a⁻¹ * (a * ε * a⁻¹) = a * (σ * ε) * a⁻¹ := by group
          _ = a * (ε * σ) * a⁻¹ := by rw [← hεσ]
          _ = a * ε * a⁻¹ * (a * σ * a⁻¹) := by group
      have hσ₁2 : σ₁ * σ₁ = 1 := by
        rw [hσ₁]
        calc a * σ * a⁻¹ * (a * σ * a⁻¹) = a * (σ * σ) * a⁻¹ := by group
          _ = 1 := by rw [hσ2']; group
      have hσ₁1 : σ₁ ≠ 1 := by
        intro h
        apply hσ1
        calc σ = a⁻¹ * (a * σ * a⁻¹) * a := by group
          _ = 1 := by rw [← hσ₁, h]; group
      have hσ₁f' : σ₁ ≠ f := by
        intro h
        apply hσε
        calc σ = a⁻¹ * (a * σ * a⁻¹) * a := by group
          _ = a⁻¹ * f * a := by rw [← hσ₁, h]
          _ = ε := by rw [← haε]; group
      have hcard := fixedField_card_pow s
      rw [hord] at hcard
      have hq : 3 < Nat.card (fixedField s) := by
        by_contra hle
        push Not at hle
        have hq2 : 2 ≤ Nat.card (fixedField s) := Finite.one_lt_card
        have hodd : Odd (Nat.card (fixedField s)) := by
          have h1 : Odd (Nat.card (fixedField s) ^ 2) := by rw [hcard]; exact hF.1
          rw [sq] at h1
          exact (Nat.odd_mul.1 h1).1
        have h3 : Nat.card (fixedField s) = 3 := by
          obtain ⟨m, hm⟩ := hodd
          omega
        apply hns
        have heven : Even (orderOf s) := by rw [hord]; exact even_two
        obtain ⟨e4⟩ := Proofs2.exists_pgl2_equiv_perm h3
        have h4 : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (α := Fin 4) (by simp)
        have h5 : Group.IsSolvable (PGL2 (fixedField s)) :=
          Group.isSolvable_of_isSolvable_injective (f := e4.toMonoidHom) e4.injective
        have h6 : Group.IsSolvable ↥(fixedSubgroup K f) :=
          Group.isSolvable_of_isSolvable_injective
            (f := (fixedSubgroupEquivPGL2 e s heven).toMonoidHom)
            (fixedSubgroupEquivPGL2 e s heven).injective
        exact Group.isSolvable_of_isSolvable_injective
          (f := (Proofs2.fixedSubgroupEquivOfConj haε).toMonoidHom)
          (Proofs2.fixedSubgroupEquivOfConj haε).injective
      set t := fieldProj e σ₁ with ht
      have hts : t * s = s * t := by
        have := congrArg (fieldProj e) hσ₁f
        rw [map_mul, map_mul, hf, fieldProj_fieldAutHom] at this
        exact this
      have ht2 : t * t = 1 := by rw [ht, ← map_mul, hσ₁2, map_one]
      have hcyc : IsCyclic (F ≃+* F) := Proofs2.isCyclic_ringAut_of_L2 hF e
      have hts' : t = 1 ∨ t = s := by
        by_cases ht1 : t = 1
        · exact Or.inl ht1
        · right
          have hto : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
          exact eq_of_orderOf_two_cyclic hto hord
      obtain ⟨A, hAD, hA2, hA1, hAf, hσ₁A⟩ : ∃ A : MulAut K, A ∈ innDiagSub e ∧ A * A = 1 ∧ A ≠ 1 ∧
          A * f = f * A ∧ (σ₁ = A ∨ σ₁ = A * f) := by
        rcases hts' with ht1 | hts1
        · exact ⟨σ₁, (mem_innDiagSub_iff e σ₁).2 ht1, hσ₁2, hσ₁1, hσ₁f, Or.inl rfl⟩
        · refine ⟨σ₁ * f, ?_, ?_, ?_, ?_, Or.inr ?_⟩
          · rw [mem_innDiagSub_iff, map_mul, ← ht, hts1, hf, fieldProj_fieldAutHom]
            exact hss
          · calc σ₁ * f * (σ₁ * f) = σ₁ * (f * σ₁) * f := by group
              _ = σ₁ * (σ₁ * f) * f := by rw [hσ₁f]
              _ = σ₁ * σ₁ * (f * f) := by group
              _ = 1 := by rw [hσ₁2, hff]; group
          · intro h
            apply hσ₁f'
            calc σ₁ = σ₁ * f * f := by rw [mul_assoc, hff, mul_one]
              _ = f := by rw [h]; group
          · calc σ₁ * f * f = σ₁ := by rw [mul_assoc, hff, mul_one]
              _ = f * (σ₁ * f) := by
                rw [← mul_assoc, ← hσ₁f, mul_assoc, hff, mul_one]
          · rw [mul_assoc, hff, mul_one]
      obtain ⟨u₁, hu₁2, hu₁1, hfu₁, hAu₁, hu₁cl, hcu₁⟩ :=
        autU_L2_field hF e s hord hq A hAD hA2 hA1 hAf
      have hσ₁u₁ : σ₁ u₁ = u₁ := by
        rcases hσ₁A with h | h
        · rw [h]
          exact hAu₁
        · rw [h]
          show A (f u₁) = u₁
          rw [hfu₁]
          exact hAu₁
      have hσ₁c : ∀ c : K, f c = c → σ₁ c = A c := by
        intro c hc
        rcases hσ₁A with h | h
        · rw [h]
        · rw [h]
          show A (f c) = A c
          rw [hc]
      refine ⟨a⁻¹ u₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [sq, ← map_mul, hu₁2, map_one]
      · intro h
        apply hu₁1
        exact (a⁻¹ : MulAut K).injective (h.trans (map_one _).symm)
      · rw [hεa', hfu₁]
      · rw [hσa', hσ₁u₁]
      · have hmap := Subgroup.mem_map_of_mem ((a⁻¹ : MulAut K) : K ≃* K).toMonoidHom hu₁cl
        rw [MonoidHom.map_closure] at hmap
        refine Subgroup.closure_mono ?_ hmap
        rintro _ ⟨x, ⟨c, hc, rfl⟩, rfl⟩
        refine ⟨a⁻¹ c, ?_, ?_⟩
        · show ε (a⁻¹ c) = a⁻¹ c
          rw [hεa']
          have : f c = c := hc
          rw [this]
        · show a⁻¹ (A c * c⁻¹) = σ (a⁻¹ c) * (a⁻¹ c)⁻¹
          rw [hσa', hσ₁c c hc]
          simp
      · intro hmem
        have hconj : MulAut.conj (a⁻¹ u₁) = a⁻¹ * MulAut.conj u₁ * a := by
          have := innAut_normal_aux u₁ (a⁻¹)
          rw [← this]
          group
        have hinn : MulAut.conj u₁ ∈ innDiagSub e := innAut_le_innDiagSub e ⟨u₁, rfl⟩
        have hback : ∀ y : MulAut K, MulAut.conj (a⁻¹ u₁) = y → MulAut.conj u₁ = a * y * a⁻¹ := by
          intro y h
          calc MulAut.conj u₁ = a * (a⁻¹ * MulAut.conj u₁ * a) * a⁻¹ := by group
            _ = a * y * a⁻¹ := by rw [← hconj, h]
        rcases hmem with h | h | h | h
        · apply hu₁1
          have h1 := hback 1 h
          rw [mul_one, mul_inv_cancel] at h1
          exact hinj (h1.trans (map_one _).symm)
        · apply hfD
          have h1 := hback ε h
          rw [haε] at h1
          rw [← h1]
          exact hinn
        · have h1 := hback σ h
          rw [← hσ₁] at h1
          rcases hσ₁A with hA' | hA'
          · exact hcu₁ (h1.trans hA')
          · have h2 : A * f ∈ innDiagSub e := by
              rw [← hA', ← h1]
              exact hinn
            exact (hfD' A hAD).1 h2
        · have h1 := hback (ε * σ) h
          have h3 : a * (ε * σ) * a⁻¹ = f * σ₁ := by
            calc a * (ε * σ) * a⁻¹ = (a * ε * a⁻¹) * (a * σ * a⁻¹) := by group
              _ = f * σ₁ := by rw [haε, ← hσ₁]
          rw [h3] at h1
          rcases hσ₁A with hA' | hA'
          · have h2 : f * A ∈ innDiagSub e := by
              rw [← hA', ← h1]
              exact hinn
            exact (hfD' A hAD).2 h2
          · have hA'' : f * σ₁ = A := by
              rw [hA']
              calc f * (A * f) = f * (f * A) := by rw [hAf]
                _ = A := by rw [← mul_assoc, hff, one_mul]
            exact hcu₁ (h1.trans hA'')

end U2Final


end CFSG.GH74.GLS.Th2.Obs
