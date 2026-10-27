module

public import CFSG.GH74.Generic.BProg.B3.S3FusionCtx
public import CFSG.GH74.Generic.BProg.B3.S3FusionPerf

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Fusion

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5
  CFSG.GH74.Generic.BProg.B1.PilotS3 CFSG.GH74.Generic.BProg Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_pair {k x y : G} (a b : G) (ha : a = x ∨ a = y ∨ a = y * x)
    (hb : b = x ∨ b = y ∨ b = y * x) (hab : a ≠ b) (hka : Commute k a) (hkb : Commute k b) :
    Commute k x ∧ Commute k y := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact absurd rfl hab
  · exact ⟨hka, hkb⟩
  · refine ⟨hka, ?_⟩
    have := hkb.mul_right hka.inv_right
    simpa [mul_assoc] using this
  · exact ⟨hkb, hka⟩
  · exact absurd rfl hab
  · refine ⟨?_, hka⟩
    have := hka.inv_right.mul_right hkb
    simpa [mul_assoc] using this
  · refine ⟨hkb, ?_⟩
    have := hka.mul_right hkb.inv_right
    simpa [mul_assoc] using this
  · refine ⟨?_, hkb⟩
    have := hkb.inv_right.mul_right hka
    simpa [mul_assoc] using this
  · exact absurd rfl hab

omit [Finite G] in
theorem conj_Z {T : Subgroup G} {m : G} (hm : m ∈ normalizer (T : Set G)) :
    ∀ z ∈ T, (∀ a ∈ T, a * z = z * a) → z * z = 1 →
      (m * z * m⁻¹ ∈ T ∧ (∀ a ∈ T, a * (m * z * m⁻¹) = (m * z * m⁻¹) * a) ∧
        (m * z * m⁻¹) * (m * z * m⁻¹) = 1) := by
  intro z hzT hzc hz2
  have hmT := mem_normalizer_iff.mp hm
  refine ⟨(hmT z).mp hzT, ?_, ?_⟩
  · intro a ha
    have ha' : m⁻¹ * a * m ∈ T := by
      refine (hmT (m⁻¹ * a * m)).mpr ?_
      have e : m * (m⁻¹ * a * m) * m⁻¹ = a := by group
      rw [e]
      exact ha
    have := hzc _ ha'
    calc a * (m * z * m⁻¹) = m * ((m⁻¹ * a * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * a * m)) * m⁻¹ := by rw [this]
      _ = (m * z * m⁻¹) * a := by group
  · calc (m * z * m⁻¹) * (m * z * m⁻¹) = m * (z * z) * m⁻¹ := by group
      _ = 1 := by rw [hz2]; group

structure Cfg (x y : G) (K T : Subgroup G) : Prop where
  gen4 : Gen4 G
  shape : BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K)
  hx : orderOf x = 2
  hy : orderOf y = 2
  hxy : x ≠ y
  hyK : y ∈ K
  hK : IsPCompIn 2 (centralizer ({x} : Set G)) K
  hT : IsSylowOf 2 T (centralizer ({x} : Set G))
  hxT : x ∈ T
  hyT : y ∈ T
  hyc : ∀ a ∈ T, a * y = y * a
  hZ : ∀ z ∈ T, (∀ a ∈ T, a * z = z * a) → z * z = 1 → z = 1 ∨ z = x ∨ z = y ∨ z = y * x

namespace Cfg

variable {x y : G} {K T : Subgroup G} (h : Cfg x y K T)

include h

theorem hx2 : x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [h.hx, pow_two] at this

theorem hy2 : y * y = 1 := by
  have := pow_orderOf_eq_one y
  rwa [h.hy, pow_two] at this

theorem hy1 : y ≠ 1 := fun e => by
  have := h.hy
  rw [e, orderOf_one] at this
  omega

theorem hyC : y ∈ centralizer ({x} : Set G) := h.hK.1 h.hyK

theorem hxc : ∀ a ∈ T, a * x = x * a := fun _ ha => mem_centralizer_singleton_iff.mp (h.hT.le ha)

theorem conj_M {m : G} (hm : m ∈ normalizer (T : Set G)) :
    ∀ g ∈ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G),
      m * g * m⁻¹ ∈ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) := by
  intro g hg
  have hgx : g * x = x * g := mem_centralizer_singleton_iff.mp hg.1
  have hgy : g * y = y * g := mem_centralizer_singleton_iff.mp hg.2
  obtain ⟨hxT', hxc', hx2'⟩ := conj_Z hm x h.hxT (fun a ha => h.hxc a ha) h.hx2
  obtain ⟨hyT', hyc', hy2'⟩ := conj_Z hm y h.hyT h.hyc h.hy2
  have hga : (m * g * m⁻¹) * (m * x * m⁻¹) = (m * x * m⁻¹) * (m * g * m⁻¹) := by
    calc (m * g * m⁻¹) * (m * x * m⁻¹) = m * (g * x) * m⁻¹ := by group
      _ = m * (x * g) * m⁻¹ := by rw [hgx]
      _ = (m * x * m⁻¹) * (m * g * m⁻¹) := by group
  have hgb : (m * g * m⁻¹) * (m * y * m⁻¹) = (m * y * m⁻¹) * (m * g * m⁻¹) := by
    calc (m * g * m⁻¹) * (m * y * m⁻¹) = m * (g * y) * m⁻¹ := by group
      _ = m * (y * g) * m⁻¹ := by rw [hgy]
      _ = (m * y * m⁻¹) * (m * g * m⁻¹) := by group
  have hne : m * x * m⁻¹ ≠ m * y * m⁻¹ := by
    intro e
    apply h.hxy
    have e1 : x = m⁻¹ * (m * x * m⁻¹) * m := by group
    have e2 : y = m⁻¹ * (m * y * m⁻¹) * m := by group
    rw [e1, e2, e]
  have hx1 : m * x * m⁻¹ ≠ 1 := fun e => by
    have := h.hx
    have e1 : x = m⁻¹ * (m * x * m⁻¹) * m := by group
    rw [e1, e] at this
    simp at this
  have hy1' : m * y * m⁻¹ ≠ 1 := fun e => by
    apply h.hy1
    have e1 : y = m⁻¹ * (m * y * m⁻¹) * m := by group
    rw [e1, e]
    group
  set k := m * g * m⁻¹ with hk
  have hxy2 : Commute k x ∧ Commute k y := by
    have ha := h.hZ _ hxT' hxc' hx2'
    have hb := h.hZ _ hyT' hyc' hy2'
    have ha' : m * x * m⁻¹ = x ∨ m * x * m⁻¹ = y ∨ m * x * m⁻¹ = y * x := by
      rcases ha with e | e | e | e
      · exact absurd e hx1
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
    have hb' : m * y * m⁻¹ = x ∨ m * y * m⁻¹ = y ∨ m * y * m⁻¹ = y * x := by
      rcases hb with e | e | e | e
      · exact absurd e hy1'
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
    exact commute_pair _ _ ha' hb' hne hga hgb
  exact ⟨mem_centralizer_singleton_iff.mpr hxy2.1.eq, mem_centralizer_singleton_iff.mpr hxy2.2.eq⟩

end Cfg

theorem exists_perfect_nbr {X : Type} [Group X] [Finite X] {xh : X} {Kb : Subgroup X}
    (h : BarShape X xh Kb) {u : X} (hu : u ∈ Kb) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ P : Subgroup X, ⁅P, P⁆ = P ∧ P ≤ Kb ∧ (∀ p ∈ P, p * u = u * p) ∧ u ∈ P := by
  classical
  obtain ⟨t, p, f, ht, hp, hp2, h5, hmod⟩ := h.model
  have hq3 : QShape3 ↥Kb := by
    refine ⟨p, f, hp, hp2, by omega, ?_⟩
    rcases ht with rfl | rfl
    · exact Or.inl hmod
    · exact Or.inr hmod
  obtain ⟨F, _, _, Pm, _, ⟨e⟩, hP⟩ := exists_equiv_grpS3_of_qShape3 hq3
  have hZ : ∀ z ∈ Kb, (∀ g ∈ Kb, g * z = z * g) → z = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥Kb) ∈ center ↥Kb := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2)
    rw [h.centerless, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hY : Split3Like F Kb := Split3Like.of_equiv e hP hZ
  have hu_ord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨J, hJK, hJ⟩ := hY.split u hu hu_ord
  obtain ⟨eJ⟩ := hJ.equiv
  have hcard : Nat.card ↥(center ↥J) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr eJ).toEquiv]
    exact CFSG.ClassicalInvolution.sl2_natCard_center hJ.odd
  have hnt : Nontrivial ↥(center ↥J) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z', hz'⟩ := exists_ne (1 : ↥(center ↥J))
  have hz'2 : z' * z' = 1 := by
    have := pow_card_eq_one' (G := ↥(center ↥J)) (x := z')
    rwa [hcard, pow_two] at this
  set zJ : X := (((z' : ↥(center ↥J)) : ↥J) : X) with hzJ
  have hzJJ : zJ ∈ J := ((z' : ↥(center ↥J)) : ↥J).2
  have hzJK : zJ ∈ Kb := hJK hzJJ
  have hzJ2 : zJ * zJ = 1 := by
    have := congrArg (fun a : ↥(center ↥J) => (((a : ↥J)) : X)) hz'2
    simpa using this
  have hzJ1 : zJ ≠ 1 := fun h1 => hz' (Subtype.ext (Subtype.ext h1))
  have hzJc : ∀ j ∈ J, j * zJ = zJ * j := by
    intro j hj
    have := Subgroup.mem_center_iff.1 z'.2 ⟨j, hj⟩
    exact congrArg Subtype.val this
  obtain ⟨g, hgK, hg⟩ := h.exists_conj_invol hzJK hu hzJ2 hzJ1 hu2 hu1
  refine ⟨J.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hJ.perfect]
  · rintro _ ⟨j, hj, rfl⟩
    exact Kb.mul_mem (Kb.mul_mem hgK (hJK hj)) (Kb.inv_mem hgK)
  · rintro _ ⟨j, hj, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg]
    have := hzJc j hj
    calc g * j * g⁻¹ * (g * zJ * g⁻¹) = g * (j * zJ) * g⁻¹ := by group
      _ = g * (zJ * j) * g⁻¹ := by rw [this]
      _ = g * zJ * g⁻¹ * (g * j * g⁻¹) := by group
  · exact ⟨zJ, hzJJ, by simpa [MulAut.conj_apply] using hg⟩

abbrev MM (x y : G) : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)

abbrev Th (x y : G) : Subgroup G := maxPerfect (MM x y)

theorem le_imgBar_Th {x y : G} (hyC : y ∈ centralizer ({x} : Set G)) (hy2 : y * y = 1)
    {P : Subgroup (CentralizerBar x)} (hP : ⁅P, P⁆ = P)
    (hPc : ∀ p ∈ P, p * piC x y = piC x y * p) : P ≤ S3.imgBar x (Th x y) := by
  classical
  have hMC : MM x y ≤ centralizer ({x} : Set G) := inf_le_left
  let f : ↥(MM x y) →* CentralizerBar x := (proj x).comp (Subgroup.inclusion hMC)
  have hu2 : (⟨y, hyC⟩ : ↥(centralizer ({x} : Set G))) * ⟨y, hyC⟩ = 1 := Subtype.ext hy2
  have hf : P ≤ f.range := by
    intro p hp
    obtain ⟨g, hg1, hg2⟩ := proj_cent x hu2 p (by rw [← piC_of_mem x hyC]; exact hPc p hp)
    have hgM : (g : G) ∈ MM x y := ⟨g.2, mem_centralizer_singleton_iff.mpr (by
      simpa using congrArg Subtype.val hg1)⟩
    exact ⟨⟨g, hgM⟩, hg2⟩
  obtain ⟨Q, hQ, hQf⟩ := exists_perfect_lift f hP hf
  have hQ' : ⁅Q.map (MM x y).subtype, Q.map (MM x y).subtype⁆ = Q.map (MM x y).subtype := by
    rw [← Subgroup.map_commutator, hQ]
  have hle : Q.map (MM x y).subtype ≤ Th x y := le_maxPerfect (Subgroup.map_subtype_le Q) hQ'
  intro p hp
  rw [← hQf] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact mem_imgBar.2 ⟨Subgroup.inclusion hMC q, hle ⟨q, hq, rfl⟩, rfl⟩

theorem eq_of_piC_eq_of_commute {x a b : G} (ha : a ∈ centralizer ({x} : Set G))
    (hb : b ∈ centralizer ({x} : Set G)) (hab : a * b = b * a) {i j : ℕ} (hai : a ^ (2 ^ i) = 1)
    (hbj : b ^ (2 ^ j) = 1) (h : piC x a = piC x b) : a = b := by
  set c : G := a⁻¹ * b with hc
  have hcC : c ∈ centralizer ({x} : Set G) :=
    (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).inv_mem ha) hb
  have hpc : piC x c = 1 := by
    rw [hc, piC_mul x ((centralizer ({x} : Set G)).inv_mem ha) hb, piC_inv x ha, h, inv_mul_cancel]
  have hodd := proj_odd x ⟨c, hcC⟩ (by rwa [piC_of_mem x hcC] at hpc)
  have hcomm : Commute a⁻¹ b := Commute.inv_left (show Commute a b from hab)
  have hA : a ^ (2 ^ (i + j)) = 1 := by rw [pow_add, pow_mul, hai, one_pow]
  have hB : b ^ (2 ^ (i + j)) = 1 := by rw [pow_add, mul_comm (2 ^ i) (2 ^ j), pow_mul, hbj, one_pow]
  have hpow : c ^ (2 ^ (i + j)) = 1 := by
    rw [hc, hcomm.mul_pow, inv_pow, hA, hB]
    simp
  have hodd' : Odd (orderOf c) := by
    have := hodd
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (orderOf c) (2 ^ (i + j)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_left.2 hodd').symm
  have h1 : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hpow)
  exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp h1)

namespace Cfg

variable {x y : G} {K T : Subgroup G} (h : Cfg x y K T)

include h

theorem yb_facts : piC x y ∈ S3.imgBar x K ∧ piC x y * piC x y = 1 ∧ piC x y ≠ 1 := by
  refine ⟨mem_imgBar.2 ⟨⟨y, h.hyC⟩, h.hyK, (piC_of_mem x h.hyC).symm⟩, ?_, fun e => ?_⟩
  · rw [← piC_mul x h.hyC h.hyC, h.hy2, piC_one]
  · have hTp : IsPGroup 2 ↥(Subgroup.zpowers y) := isPGroup_zpowers_of_involution h.hy2
    exact h.hy1 (eq_one_of_piC_eq_one hTp (Subgroup.zpowers_le.mpr h.hyC)
      (Subgroup.mem_zpowers y) e)

theorem y_mem_Th : y ∈ Th x y := by
  classical
  obtain ⟨hybK, hyb2, hyb1⟩ := h.yb_facts
  obtain ⟨P, hP, -, hPc, hyP⟩ := exists_perfect_nbr h.shape hybK hyb2 hyb1
  have hle := le_imgBar_Th h.hyC h.hy2 hP hPc
  obtain ⟨g, hgTh, hg⟩ := mem_imgBar.1 (hle hyP)
  have hgy : (g : G) * y = y * (g : G) := mem_centralizer_singleton_iff.mp (maxPerfect_le _ hgTh).2
  obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
  have hθ' : ((g ^ m : ↥(centralizer ({x} : Set G))) : G) = (g : G) ^ m := Subgroup.coe_pow _ _ _
  have hθ'Th : ((g ^ m : ↥(centralizer ({x} : Set G))) : G) ∈ Th x y := by
    rw [hθ']
    exact (Th x y).pow_mem hgTh m
  have hpi : piC x ((g ^ m : ↥(centralizer ({x} : Set G))) : G) = piC x y := by
    rw [piC_of_mem x (g ^ m).2, map_pow, hg]
    obtain ⟨k, rfl⟩ := hm
    have hyb2' : piC x y * piC x y = 1 := hyb2
    calc piC x y ^ (2 * k + 1) = (piC x y * piC x y) ^ k * piC x y := by
          rw [pow_succ, pow_mul, sq]
      _ = piC x y := by rw [hyb2', one_pow, one_mul]
  have hcomm : ((g ^ m : ↥(centralizer ({x} : Set G))) : G) * y = y * ((g ^ m : ↥(centralizer ({x} : Set G))) : G) := by
    rw [hθ']
    exact (Commute.pow_left (show Commute (g : G) y from hgy) m).eq
  have hai : (((g ^ m : ↥(centralizer ({x} : Set G))) : G)) ^ (2 ^ a) = 1 := by
    rw [hθ', ← pow_mul, mul_comm, ← hom]
    exact pow_orderOf_eq_one _
  have hbj : y ^ (2 ^ 1) = 1 := by rw [pow_one, sq]; exact h.hy2
  have := eq_of_piC_eq_of_commute (g ^ m).2 h.hyC hcomm hai hbj hpi
  exact this ▸ hθ'Th

theorem x_mem_Th {n : G} (hn : n ∈ normalizer (T : Set G)) (hnx : n * x * n⁻¹ = y) :
    x ∈ Th x y := by
  have hn' : n⁻¹ ∈ normalizer (T : Set G) := inv_mem hn
  have := conj_mem_maxPerfect (M := MM x y) (n := n⁻¹) (h.conj_M hn') h.y_mem_Th
  have e : n⁻¹ * y * n⁻¹⁻¹ = x := by rw [← hnx]; group
  rwa [e] at this

end Cfg

omit [Finite G] in
theorem imgBar_Th_perfect (x y : G) :
    ⁅S3.imgBar x (Th x y), S3.imgBar x (Th x y)⁆ = S3.imgBar x (Th x y) := by
  have hΘC : Th x y ≤ centralizer ({x} : Set G) := (maxPerfect_le _).trans inf_le_left
  let f₀ : ↥(Th x y) →* CentralizerBar x := (proj x).comp (Subgroup.inclusion hΘC)
  have hΛ : S3.imgBar x (Th x y) = f₀.range := by
    ext c
    rw [mem_imgBar, MonoidHom.mem_range]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨Subgroup.inclusion hΘC q, q.2, rfl⟩
  have hperf : Group.IsPerfect ↥(Th x y) := Subgroup.isPerfect_iff.2 (maxPerfect_perfect _)
  rw [hΛ, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  congr 1
  exact (_root_.commutator_def _).symm.trans hperf.commutator_eq_top

namespace Cfg

variable {x y : G} {K T : Subgroup G} (h : Cfg x y K T)

include h

theorem false_of_cyclic (hxTh : x ∈ Th x y)
    (hcyc : ∀ P : Subgroup (CentralizerBar x), IsPGroup 2 ↥P →
      P ≤ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) →
        IsCyclic ↥P) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb : Subgroup (CentralizerBar x) := S3.imgBar x K with hKb
  set Cb : Subgroup (CentralizerBar x) := centralizer (Kb : Set (CentralizerBar x)) with hCb
  set Λ : Subgroup (CentralizerBar x) := S3.imgBar x (Th x y) with hΛ
  have hΛperf : ⁅Λ, Λ⁆ = Λ := imgBar_Th_perfect x y
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hxΛ : xbar x ∈ Λ :=
    mem_imgBar.2 ⟨⟨x, hxC⟩, hxTh, (piC_of_mem x hxC).symm.trans (piC_x x)⟩
  have hperfΛ : Group.IsPerfect ↥Λ := Subgroup.isPerfect_iff.2 hΛperf
  have hle : ⁅Cb, Cb⁆ ≤ Cb := commutator_le_self' Cb
  have hAB : ∀ a ∈ Kb, ∀ b ∈ Cb, a * b = b * a := fun a ha b hb => mem_centralizer_iff.mp hb a ha
  let W : Subgroup (CentralizerBar x) :=
    { carrier := {g | ∃ k ∈ Kb, ∃ c ∈ ⁅Cb, Cb⁆, g = k * c}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, c₁, hc₁, rfl⟩ ⟨k₂, hk₂, c₂, hc₂, rfl⟩
        refine ⟨k₁ * k₂, Kb.mul_mem hk₁ hk₂, c₁ * c₂, mul_mem hc₁ hc₂, ?_⟩
        have e : c₁ * k₂ = k₂ * c₁ := (mem_centralizer_iff.mp (hle hc₁) k₂ hk₂).symm
        calc k₁ * c₁ * (k₂ * c₂) = k₁ * (c₁ * k₂) * c₂ := by group
          _ = k₁ * (k₂ * c₁) * c₂ := by rw [e]
          _ = k₁ * k₂ * (c₁ * c₂) := by group
      inv_mem' := by
        rintro _ ⟨k, hk, c, hc, rfl⟩
        refine ⟨k⁻¹, Kb.inv_mem hk, c⁻¹, inv_mem hc, ?_⟩
        have e : k⁻¹ * c⁻¹ = c⁻¹ * k⁻¹ := mem_centralizer_iff.mp (hle (inv_mem hc)) k⁻¹ (Kb.inv_mem hk)
        rw [mul_inv_rev, e] }
  have hΛW : Λ ≤ W := by
    calc Λ = ⁅Λ, Λ⁆ := hΛperf.symm
      _ ≤ W := by
        refine Subgroup.commutator_le.mpr fun l₁ hl₁ l₂ hl₂ => ?_
        obtain ⟨m₁, hm₁, hc₁⟩ := h.shape.perfect_le hperfΛ l₁ hl₁
        obtain ⟨m₂, hm₂, hc₂⟩ := h.shape.perfect_le hperfΛ l₂ hl₂
        have e₁ : l₁ = m₁ * (l₁ * m₁⁻¹) := by
          have := hAB m₁ hm₁ _ hc₁
          calc l₁ = (l₁ * m₁⁻¹) * m₁ := by group
            _ = m₁ * (l₁ * m₁⁻¹) := this.symm
        have e₂ : l₂ = m₂ * (l₂ * m₂⁻¹) := by
          have := hAB m₂ hm₂ _ hc₂
          calc l₂ = (l₂ * m₂⁻¹) * m₂ := by group
            _ = m₂ * (l₂ * m₂⁻¹) := this.symm
        rw [e₁, e₂, commutatorElement_mul_mul_of_commute hAB hm₁ hm₂ hc₁ hc₂]
        exact ⟨⁅m₁, m₂⁆, commutator_le_self' Kb (Subgroup.commutator_mem_commutator hm₁ hm₂),
          ⁅l₁ * m₁⁻¹, l₂ * m₂⁻¹⁆, Subgroup.commutator_mem_commutator hc₁ hc₂, rfl⟩
  obtain ⟨k, hk, c, hc, hkc⟩ := hΛW hxΛ
  have hcCb : c ∈ Cb := hle hc
  have hxCb : xbar x ∈ Cb := mem_centralizer_iff.mpr fun g _ => xbar_comm x g
  have hkCb : k ∈ Cb := by
    have : k = xbar x * c⁻¹ := by rw [hkc]; group
    rw [this]
    exact Cb.mul_mem hxCb (Cb.inv_mem hcCb)
  have hk1 : k = 1 := by
    have hmem : (⟨k, hk⟩ : ↥Kb) ∈ center ↥Kb := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp hkCb g g.2)
    rw [h.shape.centerless, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hxc : xbar x = c := by rw [hkc, hk1, one_mul]
  have hcomm : xbar x ∈ ⁅Cb, Cb⁆ := hxc ▸ hc
  have hsub : ⁅Cb, Cb⁆ ≤ (_root_.commutator ↥Cb).map Cb.subtype := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ⟨⁅(⟨a, ha⟩ : ↥Cb), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  obtain ⟨z, hz, hzx⟩ := hsub hcomm
  have hz2 : z * z = 1 := by
    apply Subtype.ext
    have : (z : CentralizerBar x) = xbar x := hzx
    simp only [Subgroup.coe_mul, this, Subgroup.coe_one]
    exact xbar_mul_self h.hx
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥Cb) := inferInstance
  have hP' : IsCyclic ↥((P : Subgroup ↥Cb).map Cb.subtype) :=
    hcyc _ (P.isPGroup'.map _) (Subgroup.map_subtype_le _)
  have hPcyc : IsCyclic ↥(P : Subgroup ↥Cb) :=
    isCyclic_of_surjective (Subgroup.equivMapOfInjective (P : Subgroup ↥Cb) Cb.subtype
      Cb.subtype_injective).symm.toMonoidHom (Subgroup.equivMapOfInjective _ _ Cb.subtype_injective).symm.surjective
  have hz1 := eq_one_of_mem_commutator_of_cyclic_sylow P hPcyc hz hz2
  apply xbar_ne_one h.hx
  rw [← hzx, hz1]
  rfl

end Cfg

theorem conj_mem_centralizer_of_normal {X : Type} [Group X] {Kb : Subgroup X} (hKb : Kb.Normal) {c : X}
    (hc : c ∈ centralizer (Kb : Set X)) (g : X) : g * c * g⁻¹ ∈ centralizer (Kb : Set X) := by
  rw [mem_centralizer_iff]
  intro k hk
  have hk' : g⁻¹ * k * g ∈ Kb := by simpa using hKb.conj_mem k hk g⁻¹
  have := mem_centralizer_iff.mp hc _ hk'
  calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [this]
    _ = (g * c * g⁻¹) * k := by group

theorem exists_F {x : G} {K T A : Subgroup G}
    (hshape : BarShape (CentralizerBar x) (xbar x) (S3.imgBar x K))
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hsrc : IsSource2 x K A) :
    ∃ F : Subgroup G, F ≤ T ∧ Nat.card ↥F = 8 ∧ (∀ f ∈ F, f * f = 1) ∧
      (∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ * f₂ = f₂ * f₁) ∧
      ∀ f ∈ F, ∀ c ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
        Set (CentralizerBar x)), piC x f * c = c * piC x f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAC, hAel, hAcard, hAcase⟩ := hsrc
  have hAp : IsPGroup 2 ↥A := IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)
  obtain ⟨T', hT', hAT'⟩ := S3.exists_isSylowOf_ge hAC hAp
  obtain ⟨k, hkC, hk⟩ := hT.exists_mem_conj hT'
  set Cb : Subgroup (CentralizerBar x) :=
    centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x)) with hCb
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hAc : ∀ a ∈ A, ∀ c ∈ Cb, piC x a * c = c * piC x a := by
    have hKbc : ∀ e ∈ K, ∀ c ∈ Cb, piC x e * c = c * piC x e := fun e he c hc =>
      mem_centralizer_iff.mp hc _ (mem_imgBar.2 ⟨⟨e, hK.1 he⟩, he, (piC_of_mem x (hK.1 he)).symm⟩)
    let Sg : Subgroup G := ((centralizer (Cb : Set (CentralizerBar x))).comap (proj x)).map
      (centralizer ({x} : Set G)).subtype
    have hSg : ∀ g : G, g ∈ Sg ↔ ∃ hg : g ∈ centralizer ({x} : Set G),
        proj x ⟨g, hg⟩ ∈ centralizer (Cb : Set (CentralizerBar x)) := by
      intro g
      constructor
      · rintro ⟨g', hg', rfl⟩
        exact ⟨g'.2, hg'⟩
      · rintro ⟨hg, hg'⟩
        exact ⟨⟨g, hg⟩, hg', rfl⟩
    have hxSg : x ∈ Sg := (hSg x).2 ⟨hxC, mem_centralizer_iff.mpr fun c hc => by
      have : proj x ⟨x, hxC⟩ = xbar x := (piC_of_mem x hxC).symm.trans (piC_x x)
      rw [this]
      exact xbar_comm x c⟩
    have hAle : A ≤ Sg := by
      rcases hAcase with ⟨hAK, -⟩ | ⟨E, hEK, hAE, -⟩
      · intro a ha
        refine (hSg a).2 ⟨hAC ha, mem_centralizer_iff.mpr fun c hc => ?_⟩
        have := hKbc a (hAK ha) c hc
        rw [← piC_of_mem x (hAC ha)] at *
        exact this.symm
      · rw [hAE]
        refine sup_le (fun e he => (hSg e).2 ⟨hK.1 (hEK he), mem_centralizer_iff.mpr fun c hc => ?_⟩) ?_
        · have := hKbc e (hEK he) c hc
          rw [piC_of_mem x (hK.1 (hEK he))] at this
          exact this.symm
        · exact Subgroup.zpowers_le.mpr hxSg
    intro a ha c hc
    obtain ⟨haC, hh⟩ := (hSg a).1 (hAle ha)
    rw [piC_of_mem x haC]
    exact (mem_centralizer_iff.mp hh c hc).symm
  refine ⟨A.map (MulAut.conj k⁻¹).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact (hk _).mp (hAT' ha)
  · rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hAcard]
  · rintro _ ⟨a, ha, rfl⟩
    have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc k⁻¹ * a * k * (k⁻¹ * a * k) = k⁻¹ * (a * a) * k := by group
      _ = 1 := by rw [← pow_two, ha2]; group
  · rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩
    have : IsElementaryAbelian 2 ↥A := hAel
    have hcomm : a₁ * a₂ = a₂ * a₁ := congrArg Subtype.val (mul_comm' (⟨a₁, ha₁⟩ : ↥A) ⟨a₂, ha₂⟩)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc k⁻¹ * a₁ * k * (k⁻¹ * a₂ * k) = k⁻¹ * (a₁ * a₂) * k := by group
      _ = k⁻¹ * (a₂ * a₁) * k := by rw [hcomm]
      _ = k⁻¹ * a₂ * k * (k⁻¹ * a₁ * k) := by group
  · rintro _ ⟨a, ha, rfl⟩ c hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have haC : a ∈ centralizer ({x} : Set G) := hAC ha
    have hkiC : k⁻¹ ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).inv_mem hkC
    have hpf : piC x (k⁻¹ * a * k) = (piC x k)⁻¹ * piC x a * piC x k := by
      rw [piC_mul x ((centralizer ({x} : Set G)).mul_mem hkiC haC) hkC, piC_mul x hkiC haC,
        piC_inv x hkC]
    rw [hpf]
    have hc' := conj_mem_centralizer_of_normal hshape.normal hc (piC x k)
    have h1 := hAc a ha _ hc'
    calc (piC x k)⁻¹ * piC x a * piC x k * c
        = (piC x k)⁻¹ * (piC x a * (piC x k * c * (piC x k)⁻¹)) * piC x k := by group
      _ = (piC x k)⁻¹ * ((piC x k * c * (piC x k)⁻¹) * piC x a) * piC x k := by rw [h1]
      _ = c * ((piC x k)⁻¹ * piC x a * piC x k) := by group

end S3Fusion

end CFSG.GH74.Generic.BProg.B3
