module

public import CFSG.GH74.Generic.BProg.B3.S3FusionSDFin
public import CFSG.GH74.Generic.BProg.B3.S3FusionI
public import CFSG.GH74.Generic.BProg.B3.S3FusionCore
public import CFSG.GH74.Generic.BProg.B3.S3L3Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def Prop301Concl (x y : G) (T : Subgroup G) : Prop :=
  (∃ n ∈ normalizer (T : Set G) ⊓ centralizer ({y} : Set G), n * x * n⁻¹ = x * y) ∧
    (∀ g : G, g * x * g⁻¹ ≠ y) ∧
    (∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ ∀ s ∈ S, s * y = y * s) ∧
    (∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ¬ ∀ s ∈ S, s * x = x * s) ∧
    x ∈ (_root_.commutator ↥(centralizer ({y} : Set G))).map (centralizer ({y} : Set G)).subtype

namespace S3FusionT

omit [Finite G] in
theorem conj_pow_odd {x y n : G} (hy2 : y * y = 1) (hnx : n * x * n⁻¹ = x * y)
    (hny : n * y * n⁻¹ = y) (k : ℕ) : (n ^ (2 * k + 1)) * x * (n ^ (2 * k + 1))⁻¹ = x * y := by
  have hxy : n * (x * y) * n⁻¹ = x := by
    calc n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
      _ = x * y * y := by rw [hnx, hny]
      _ = x := by rw [mul_assoc, hy2, mul_one]
  induction k with
  | zero => simpa using hnx
  | succ k ih =>
    have e : n ^ (2 * (k + 1) + 1) = n * n * n ^ (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by ring, pow_add, pow_two]
    rw [e]
    calc n * n * n ^ (2 * k + 1) * x * (n * n * n ^ (2 * k + 1))⁻¹
        = n * (n * (n ^ (2 * k + 1) * x * (n ^ (2 * k + 1))⁻¹) * n⁻¹) * n⁻¹ := by group
      _ = n * (n * (x * y) * n⁻¹) * n⁻¹ := by rw [ih]
      _ = n * x * n⁻¹ := by rw [hxy]
      _ = x * y := hnx

theorem not_central_of_swap {x y : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hy2 : y * y = 1) (hy1 : y ≠ 1) {n : G}
    (hn : n ∈ normalizer (T : Set G)) (hnx : n * x * n⁻¹ = x * y) (hny : n * y * n⁻¹ = y) :
    ∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ¬ ∀ s ∈ S, s * x = x * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS hSx
  have hSC : S ≤ centralizer ({x} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hSx s hs)
  obtain ⟨T', hT', hST'⟩ := S3.exists_isSylowOf_ge hSC hS.isPGroup
  have hT'S : T' = S := hS.eq_of_le hST' le_top hT'.isPGroup
  have hcard : Nat.card T = 2 ^ (Nat.card (⊤ : Subgroup G)).factorization 2 := by
    rw [hT.card_eq, ← hT'.card_eq, hT'S, hS.card_eq]
  have hTG : IsSylowOf 2 T ⊤ := isSylowOf_of_card le_top hcard
  obtain ⟨hle, hTp, hdvd⟩ := isSylowOf_iff.1 hTG
  let Q : Sylow 2 G := hTp.toSylow (by rwa [Subgroup.relIndex_top_right] at hdvd)
  have hQ : (Q : Subgroup G) = T := IsPGroup.toSylow_coe hTp _
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  have hbpos : b ≠ 0 := by
    obtain ⟨k, hk⟩ := hb
    omega
  have hord : orderOf (n ^ b) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hbpos (hab ▸ dvd_mul_left b _), hab,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hbpos)]
  have hpg : IsPGroup 2 ↥(Subgroup.zpowers (n ^ b)) :=
    IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hord])
  have hnQ : n ^ b ∈ normalizer (Q : Set G) := by
    rw [← Sylow.coe_coe, hQ]
    exact (normalizer (T : Set G)).pow_mem hn b
  have hmem : n ^ b ∈ Subgroup.zpowers (n ^ b) ⊓ normalizer (Q : Set G) :=
    ⟨Subgroup.mem_zpowers _, hnQ⟩
  rw [hpg.inf_normalizer_sylow Q] at hmem
  have hbT : n ^ b ∈ T := by
    rw [← hQ]
    exact hmem.2
  have hbx : n ^ b * x = x * n ^ b := mem_centralizer_singleton_iff.mp (hT.le hbT)
  obtain ⟨k, hk⟩ := hb
  have hconj := conj_pow_odd hy2 hnx hny k
  rw [← hk] at hconj
  have hxy : x * y = x := by
    calc x * y = n ^ b * x * (n ^ b)⁻¹ := hconj.symm
      _ = x * n ^ b * (n ^ b)⁻¹ := by rw [hbx]
      _ = x := by group
  exact hy1 (mul_left_cancel (hxy.trans (mul_one x).symm))

end S3FusionT

theorem prop301_coreT (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x ≠ y) {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hxT : x ∈ T) (hyT : y ∈ T)
    (hyc : ∀ a ∈ T, a * y = y * a)
    (hZ : ∀ z ∈ T, (∀ a ∈ T, a * z = z * a) → z * z = 1 → z = 1 ∨ z = x ∨ z = y ∨ z = y * x)
    (hI : (∃ g : G, g * x * g⁻¹ = y) ∨ (∃ g : G, g * x * g⁻¹ = x * y))
    (hII : ∀ n ∈ normalizer (T : Set G), n * x * n⁻¹ ≠ y) : Prop301Concl x y T := by
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hy1 : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy
    omega
  have hxc : ∀ a ∈ T, a * x = x * a := fun a ha => mem_centralizer_singleton_iff.mp (hT.le ha)
  have hxyc : x * y = y * x := hyc x hxT
  have hb : ∀ g : G, g * x * g⁻¹ ≠ y := by
    intro g hg
    obtain ⟨n, hn', hnx⟩ := exists_normalizer_conj hT g (fun a ha => by rw [hg]; exact hyc a ha)
    exact hII n hn' (hnx.trans hg)
  obtain ⟨g₀, hg₀⟩ : ∃ g : G, g * x * g⁻¹ = x * y := by
    rcases hI with ⟨g, hg⟩ | h
    · exact absurd hg (hb g)
    · exact h
  obtain ⟨n, hn', hnx⟩ := exists_normalizer_conj hT g₀ (fun a ha => by
    rw [hg₀]
    calc a * (x * y) = (a * x) * y := (mul_assoc _ _ _).symm
      _ = (x * a) * y := by rw [hxc a ha]
      _ = x * (a * y) := mul_assoc _ _ _
      _ = x * (y * a) := by rw [hyc a ha]
      _ = (x * y) * a := (mul_assoc _ _ _).symm)
  have hnx' : n * x * n⁻¹ = x * y := hnx.trans hg₀
  have hnT := mem_normalizer_iff.mp hn'
  have hwT : n * y * n⁻¹ ∈ T := (hnT y).mp hyT
  have hwc : ∀ a ∈ T, a * (n * y * n⁻¹) = (n * y * n⁻¹) * a := by
    intro a ha
    have ha' : n⁻¹ * a * n ∈ T := by
      refine (hnT (n⁻¹ * a * n)).mpr ?_
      have e : n * (n⁻¹ * a * n) * n⁻¹ = a := by group
      rw [e]
      exact ha
    have := hyc _ ha'
    calc a * (n * y * n⁻¹) = n * ((n⁻¹ * a * n) * y) * n⁻¹ := by group
      _ = n * (y * (n⁻¹ * a * n)) * n⁻¹ := by rw [this]
      _ = (n * y * n⁻¹) * a := by group
  have hw2 : (n * y * n⁻¹) * (n * y * n⁻¹) = 1 := by
    calc (n * y * n⁻¹) * (n * y * n⁻¹) = n * (y * y) * n⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hw : n * y * n⁻¹ = y := by
    rcases hZ _ hwT hwc hw2 with h1 | h1 | h1 | h1
    · exfalso
      apply hy1
      have : y = n⁻¹ * (n * y * n⁻¹) * n := by group
      rw [this, h1]
      group
    · exfalso
      apply hb n⁻¹
      rw [inv_inv]
      calc n⁻¹ * x * n = n⁻¹ * (n * y * n⁻¹) * n := by rw [h1]
        _ = y := by group
    · exact h1
    · exfalso
      apply hxy
      have h3 : n * y * n⁻¹ = n * x * n⁻¹ := by rw [h1, hnx', hxyc]
      have e1 : y = n⁻¹ * (n * y * n⁻¹) * n := by group
      have e2 : x = n⁻¹ * (n * x * n⁻¹) * n := by group
      rw [e1, e2, h3]
  have hxC : x ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.mpr hxyc
  have hweak : ∀ z : G, z ∈ T → (∀ a ∈ T, a * z = z * a) → z * z = 1 → (∃ g : G, g * y * g⁻¹ = z) →
      z = y := by
    intro z hzT hzc hzz ⟨g, hg⟩
    rcases hZ z hzT hzc hzz with h | h | h | h
    · exfalso
      apply hy1
      have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [this, hg, h]
      group
    · exfalso
      apply hb g⁻¹
      rw [inv_inv]
      calc g⁻¹ * x * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [hg, h]
        _ = y := by group
    · exact h
    · exfalso
      apply hb (g⁻¹ * n)
      have h3 : g * y * g⁻¹ = n * x * n⁻¹ := by rw [hg, h, hnx', hxyc]
      calc g⁻¹ * n * x * (g⁻¹ * n)⁻¹ = g⁻¹ * (n * x * n⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [h3]
        _ = y := by group
  obtain ⟨S, hS, hyS, hySc⟩ := exists_sylow_central_of_weakly_closed hT hxT hyT hyc hy2 hweak
  have hd : ∃ hx' : x ∈ centralizer ({y} : Set G),
      (⟨x, hx'⟩ : ↥(centralizer ({y} : Set G))) ∈
        _root_.commutator ↥(centralizer ({y} : Set G)) := by
    refine S45.b_III8_6_3 G hs hn x hx T hT y hyT hyc hy ⟨S, hS, hyS, hySc⟩ ?_
    intro g hgP hgc
    have hz2 : (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
      calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = 1 := by rw [hy2]; group
    exact ⟨1, Subgroup.one_mem _, by rw [hweak _ hgP hgc hz2 ⟨g, rfl⟩]; group⟩
  refine ⟨⟨n, Subgroup.mem_inf.mpr ⟨hn', mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp hw)⟩, hnx'⟩, hb, ⟨S, hS, hySc⟩,
    S3FusionT.not_central_of_swap hT hy2 hy1 hn' hnx' hw, ?_⟩
  obtain ⟨hx', hmem⟩ := hd
  exact ⟨⟨x, hx'⟩, hmem, rfl⟩

theorem cfg_of_setup30 {x y : G} {K A T : Subgroup G} (h : Setup30 G x K A y) (hT : IsZT x y T) :
    S3Fusion.Cfg x y K T := by
  classical
  obtain ⟨hTS, hxT, hyT, hyc, hZ'⟩ := hT
  have hx : orderOf x = 2 := h.circ.1.1.1.1
  have hy : orderOf y = 2 := h.y_ord
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  have hyK : y ∈ K := (Subgroup.mem_inf.1 h.y_mem).2
  have hyC : y ∈ centralizer ({x} : Set G) := hK.1 hyK
  have hshape := S3Fusion.barShape_of_ctx h.hyp.gen4 hx hK h.shape h.rank1
  have hxy : x ≠ y := by
    intro e
    apply hshape.xh_notin
    have hybK : piC x y ∈ S3.imgBar x K := mem_imgBar.2 ⟨⟨y, hyC⟩, hyK, (piC_of_mem x hyC).symm⟩
    have hpx : piC x y = xbar x := by
      rw [← e]
      exact piC_x x
    rw [← hpx]
    exact hybK
  have hxyc : x * y = y * x := hyc x hxT
  have hZ : ∀ z ∈ T, (∀ a ∈ T, a * z = z * a) → z * z = 1 → z = 1 ∨ z = x ∨ z = y ∨ z = y * x := by
    intro z hz hzc hz2
    rcases hZ' z hz hzc hz2 with e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (e.trans hxyc)))
  exact ⟨h.hyp.gen4, hshape, hx, hy, hxy, hyK, hK, hTS, hxT, hyT, hyc, hZ⟩

theorem prop301T_of_outer {x y : G} {K A T : Subgroup G} (h : Setup30 G x K A y) (hT : IsZT x y T)
    (hOuter : S3Fusion.OuterCaseFusion x K y) :
    (∃ n ∈ normalizer (T : Set G) ⊓ centralizer ({y} : Set G), n * x * n⁻¹ = x * y) ∧
      (∀ g : G, g * x * g⁻¹ ≠ y) ∧
      (∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ ∀ s ∈ S, s * y = y * s) ∧
      (∀ S : Subgroup G, IsSylowOf 2 S ⊤ → ¬ ∀ s ∈ S, s * x = x * s) ∧
      x ∈ (_root_.commutator ↥(centralizer ({y} : Set G))).map
        (centralizer ({y} : Set G)).subtype := by
  classical
  have hcfg := cfg_of_setup30 h hT
  obtain ⟨hTS, hxT, hyT, hyc, hZ'⟩ := hT
  have hxyc : x * y = y * x := hyc x hxT
  have hZ : ∀ z ∈ T, (∀ a ∈ T, a * z = z * a) → z * z = 1 → z = 1 ∨ z = x ∨ z = y ∨ z = y * x := by
    intro z hz hzc hz2
    rcases hZ' z hz hzc hz2 with e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (e.trans hxyc)))
  have hI := S3Fusion.lemma302 h.hyp.simple h.hyp.nonab hcfg.shape hcfg.hx (hcfg.hK.1 hcfg.hyK)
    hcfg.hyK
    hcfg.hy hTS hxT hOuter
  exact prop301_coreT h.hyp.simple h.hyp.nonab hcfg.hx hcfg.hy hcfg.hxy hTS hxT hyT hyc hZ hI
    (fun n hn hnx => hcfg.no_normalizer_conj h.src hn hnx)

end CFSG.GH74.Generic.BProg.B3
