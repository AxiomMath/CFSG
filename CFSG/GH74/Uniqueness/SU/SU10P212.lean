module

public import CFSG.GH74.Uniqueness.SU.SU10P212A
public import CFSG.GH74.Uniqueness.SU.SU10Hyp
public import CFSG.GH74.Uniqueness.SU.SU10BenderTypes
public import CFSG.GH74.Uniqueness.SU.SU10Alt
public import CFSG.GH74.Uniqueness.SU.SU10Z
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldArithmetic

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8

section Core

variable {G : Type} [Group G] [Finite G] {u : G}

abbrev piU (u : G) :
    ↥(centralizer ({u} : Set G)) →* Hbar (centralizer ({u} : Set G)) :=
  QuotientGroup.mk' (pPrimeCore 2 (centralizer ({u} : Set G)))

theorem endgame212 {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp21 S M z)
    (hu2 : orderOf u = 2) (huZ : ¬ IsConj z u)
    {K₁ : Subgroup (Hbar (centralizer ({u} : Set G)))} [K₁.Normal] (hwK : zbar u ∉ K₁)
    (htype : ∀ t : Hbar (centralizer ({u} : Set G)), t * t = 1 → t ∈ K₁ ∨ t * zbar u ∈ K₁)
    (hconj0 : ∀ a b : Hbar (centralizer ({u} : Set G)), a ∈ K₁ → b ∈ K₁ → orderOf a = 2 →
      orderOf b = 2 → ∃ c, c⁻¹ * a * c = b)
    (hconj1 : ∀ a b : Hbar (centralizer ({u} : Set G)), a * zbar u ∈ K₁ → b * zbar u ∈ K₁ →
      orderOf a = 2 → orderOf b = 2 → a ≠ zbar u → b ≠ zbar u → ∃ c, c⁻¹ * a * c = b)
    {x y : G} (hx : IsConj z x) (hy : IsConj z y) (hxy : x * y = y * x) (hu : u = x * y) :
    False := by
  classical
  have hz2 : orderOf z = 2 := h.z_invol
  have hx2 : orderOf x = 2 := orderOf_eq_two_of_isConj hz2 hx
  have hy2 : orderOf y = 2 := orderOf_eq_two_of_isConj hz2 hy
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, sq] at this
  have hxu : x * u = u * x := by
    rw [hu]
    calc x * (x * y) = x * (y * x) := by rw [hxy]
      _ = x * y * x := by group
  have hyu : y * u = u * y := by
    rw [hu]
    calc y * (x * y) = (y * x) * y := by group
      _ = (x * y) * y := by rw [← hxy]
  have hxH : x ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hxu
  have hyH : y ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hyu
  have huH : u ∈ centralizer ({u} : Set G) := mem_centralizer_self u
  have hūū : zbar u * zbar u = 1 := by
    have := pow_orderOf_eq_one (zbar u)
    rwa [zbar_orderOf hu2, sq] at this
  have hxyb : piU u ⟨x, hxH⟩ * piU u ⟨y, hyH⟩ = zbar u := by
    rw [← map_mul]
    have : (⟨x, hxH⟩ : ↥(centralizer ({u} : Set G))) * ⟨y, hyH⟩ = ⟨u, huH⟩ :=
      Subtype.ext hu.symm
    rw [this]
    rfl
  have key : ∀ (a b : G) (ha : a ∈ centralizer ({u} : Set G))
      (hb : b ∈ centralizer ({u} : Set G)), orderOf a = 2 → orderOf b = 2 → IsConj z a →
      IsConj z b → piU u ⟨a, ha⟩ ∈ K₁ → piU u ⟨b, hb⟩ * zbar u ∈ K₁ → False := by
    intro a b ha hb ha2 hb2 haZ hbZ ha0 hb1
    obtain ⟨g, hgne, hgcomm⟩ := exists_commuting_conj_ne h.simple h.nonab hu2
    have hu'H : g * u * g⁻¹ ∈ centralizer ({u} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgcomm
    have hu'2 : orderOf (g * u * g⁻¹) = 2 := by simpa [hu2] using (MulAut.conj g).orderOf_eq u
    have hu'u : IsConj u (g * u * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
    have hu'ne : piU u ⟨g * u * g⁻¹, hu'H⟩ ≠ zbar u := fun h1 =>
      hgne (eq_of_map_eq_central hu2 hu'2 hu'H h1)
    have hbne : piU u ⟨b, hb⟩ ≠ zbar u := fun h1 => huZ ((eq_of_map_eq_central hu2 hb2 hb h1) ▸ hbZ)
    have hu'sq : g * u * g⁻¹ * (g * u * g⁻¹) = 1 := by
      calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by
          have huu : u * u = 1 := by
            have := pow_orderOf_eq_one u
            rwa [hu2, sq] at this
          rw [huu]
          group
    have hu'sqb := map_mul_self_eq_one hu'H hu'sq
    suffices hzu' : IsConj z (g * u * g⁻¹) from huZ (hzu'.trans hu'u.symm)
    rcases htype _ hu'sqb with h1 | h1
    · obtain ⟨c, hc⟩ := hconj0 _ _ ha0 h1 (hbar_orderOf ha2 ha) (hbar_orderOf hu'2 hu'H)
      obtain ⟨c', -, hc'⟩ := exists_conj_of_bar_conj ha hu'H ha2 hu'2 ⟨c, hc⟩
      exact haZ.trans (isConj_iff.mpr ⟨c'⁻¹, by simpa using hc'⟩)
    · obtain ⟨c, hc⟩ := hconj1 _ _ hb1 h1 (hbar_orderOf hb2 hb) (hbar_orderOf hu'2 hu'H) hbne hu'ne
      obtain ⟨c', -, hc'⟩ := exists_conj_of_bar_conj hb hu'H hb2 hu'2 ⟨c, hc⟩
      exact hbZ.trans (isConj_iff.mpr ⟨c'⁻¹, by simpa using hc'⟩)
  have hxxb := map_mul_self_eq_one hxH hxx
  have hyyb := map_mul_self_eq_one hyH hyy
  rcases htype _ hxxb with hx0 | hx1 <;> rcases htype _ hyyb with hy0 | hy1
  · exact hwK (hxyb ▸ K₁.mul_mem hx0 hy0)
  · exact key x y hxH hyH hx2 hy2 hx hy hx0 hy1
  · exact key y x hyH hxH hy2 hx2 hy hx hy0 hx1
  · apply hwK
    have h3 : piU u ⟨x, hxH⟩ * zbar u * (piU u ⟨y, hyH⟩ * zbar u) = zbar u := by
      calc piU u ⟨x, hxH⟩ * zbar u * (piU u ⟨y, hyH⟩ * zbar u)
          = piU u ⟨x, hxH⟩ * (zbar u * piU u ⟨y, hyH⟩) * zbar u := by group
        _ = piU u ⟨x, hxH⟩ * (piU u ⟨y, hyH⟩ * zbar u) * zbar u := by
          rw [← zbar_central u (piU u ⟨y, hyH⟩)]
        _ = (piU u ⟨x, hxH⟩ * piU u ⟨y, hyH⟩) * (zbar u * zbar u) := by group
        _ = zbar u := by rw [hxyb, hūū, mul_one]
    rw [← h3]
    exact K₁.mul_mem hx1 hy1

theorem core212
    (hKI6 : K.KI6) {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp21 S M z)
    (hHM : centralizer ({z} : Set G) ≤ M) (hu2 : orderOf u = 2)
    (huS : u ∈ (S : Subgroup G))
    (hext : IsSylowIn (centralizer ({u} : Set G)) ((S : Subgroup G) ⊓ centralizer ({u} : Set G)))
    {x y : G} (hx : IsConj z x) (hy : IsConj z y) (hxy : x * y = y * x) (hu : u = x * y) :
    centralizer ({u} : Set G) ≤ M := by
  classical
  by_contra hHM'
  have hrank2 : 2 ≤ Open.pRank 2 (S : Subgroup G) := le_trans (by norm_num) h.rank
  have hSM : (S : Subgroup G) ≤ M := (le_gammaTwo_self hrank2).trans h.gamma_le
  have huM : u ∈ M := hSM huS
  have huZ : ¬ IsConj z u := fun hc => hHM' (centralizer_le_of_conj h hHM hc huM)
  have hzS : z ∈ (S : Subgroup G) := h.z_mem
  have hzu : z * u = u * z := (h.z_center u huS).symm
  have huH : u ∈ centralizer ({u} : Set G) := mem_centralizer_self u
  have hzH : z ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hzu
  have huP : u ∈ (S : Subgroup G) ⊓ centralizer ({u} : Set G) := Subgroup.mem_inf.mpr ⟨huS, huH⟩
  have hzP : z ∈ (S : Subgroup G) ⊓ centralizer ({u} : Set G) := Subgroup.mem_inf.mpr ⟨hzS, hzH⟩
  have hrankP : 3 ≤ Open.pRank 2 ((S : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
    rw [pRank_eq_of_isSylowIn hext]
    exact rank3_centralizer h hu2
  have h21A : ∀ Q : Subgroup G, Q ≤ (S : Subgroup G) ⊓ centralizer ({u} : Set G) →
      2 ≤ Open.pRank 2 Q → normalizer (Q : Set G) ⊓ centralizer ({u} : Set G) ≤ M :=
    fun Q hQP hQ g hg => h.gamma_le (normalizer_le_gammaTwo (hQP.trans inf_le_left) hQ hg.1)
  obtain ⟨-, K₁, hcomp, -, hC, hcases, hbc⟩ := ki6_concl hKI6 h.kgh
    (centralizer_ne_top_of_order_two h hu2) hext hrankP hu2 huH
    (fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg) h21A hHM'
  have hT0 : ((sylowMap (sylowIn hext) : Sylow 2 (Hbar (centralizer ({u} : Set G)))) : Subgroup (Hbar (centralizer ({u} : Set G)))) =
      hbarImage (centralizer ({u} : Set G)) ((S : Subgroup G) ⊓ centralizer ({u} : Set G)) :=
    coe_sylowMap_sylowIn hext
  generalize (sylowMap (sylowIn hext) : Sylow 2 (Hbar (centralizer ({u} : Set G)))) = T' at hcases hbc hT0
  have huT : zbar u ∈ (T' : Subgroup (Hbar (centralizer ({u} : Set G)))) := by
    rw [hT0]
    exact zbar_mem_hbarImage huP
  have hzT : piU u ⟨z, hzH⟩ ∈ (T' : Subgroup (Hbar (centralizer ({u} : Set G)))) := by
    rw [hT0]
    exact map_mem_hbarImage inf_le_right hzP
  have hnc : ¬ IsCyclic ↥(center ↥(T' : Subgroup (Hbar (centralizer ({u} : Set G))))) := by
    intro hcyc
    have h1 : (⟨zbar u, huT⟩ : ↥(T' : Subgroup (Hbar (centralizer ({u} : Set G))))) ∈ center ↥(T' : Subgroup (Hbar (centralizer ({u} : Set G)))) := by
      rw [Subgroup.mem_center_iff]
      intro t
      exact Subtype.ext (zbar_central u t)
    have h2 : (⟨piU u ⟨z, hzH⟩, hzT⟩ : ↥(T' : Subgroup (Hbar (centralizer ({u} : Set G))))) ∈ center ↥(T' : Subgroup (Hbar (centralizer ({u} : Set G)))) := by
      rw [Subgroup.mem_center_iff]
      intro t
      have ht : (t : Hbar (centralizer ({u} : Set G))) ∈
          hbarImage (centralizer ({u} : Set G)) ((S : Subgroup G) ⊓ centralizer ({u} : Set G)) :=
        (SetLike.ext_iff.mp hT0 _).mp t.2
      obtain ⟨p, hp, hpt⟩ := ht
      have hpS : (p : G) ∈ (S : Subgroup G) := (Subgroup.mem_subgroupOf.mp hp).1
      have hzp : (⟨z, hzH⟩ : ↥(centralizer ({u} : Set G))) * p = p * ⟨z, hzH⟩ :=
        Subtype.ext (h.z_center p hpS).symm
      apply Subtype.ext
      show (t : Hbar (centralizer ({u} : Set G))) * piU u ⟨z, hzH⟩ = piU u ⟨z, hzH⟩ * (t : Hbar (centralizer ({u} : Set G)))
      rw [← hpt, ← map_mul, ← map_mul, hzp]
    have ho1 : orderOf (⟨⟨zbar u, huT⟩, h1⟩ : ↥(center ↥(T' : Subgroup (Hbar (centralizer ({u} : Set G)))))) = 2 :=
      (Subgroup.orderOf_coe _).symm.trans ((Subgroup.orderOf_coe _).symm.trans (zbar_orderOf hu2))
    have ho2 : orderOf (⟨⟨piU u ⟨z, hzH⟩, hzT⟩, h2⟩ : ↥(center ↥(T' : Subgroup (Hbar (centralizer ({u} : Set G)))))) = 2 :=
      (Subgroup.orderOf_coe _).symm.trans ((Subgroup.orderOf_coe _).symm.trans
        (hbar_orderOf h.z_invol hzH))
    have := hcyc
    have heq := CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.cyclic_involutions_eq
      (⟨⟨zbar u, huT⟩, h1⟩ : ↥(center ↥(T' : Subgroup (Hbar (centralizer ({u} : Set G)))))) ⟨⟨piU u ⟨z, hzH⟩, hzT⟩, h2⟩ ho1 ho2
    have hee : zbar u = piU u ⟨z, hzH⟩ := by simpa using heq
    have hzu' : z = u := eq_of_map_eq hext hzP huP hee.symm
    apply huZ
    rw [← hzu']
  have hBender := hbc.resolve_right hnc
  rcases hcases with ⟨hKn, -, -, hle⟩ | ⟨hSL, -⟩ | ⟨-, hK₁alt, -⟩ | ⟨hSz, -⟩
  · have := hKn
    obtain ⟨hwK, htype, hconj0, hconj1⟩ := bender_types T' hBender (zbar_orderOf hu2)
      (zbar_central u) huT hC hle
    exact endgame212 h hu2 huZ hwK htype hconj0 hconj1 hx hy hxy hu
  · exact center_ne_bot_of_isSL25 hSL (center_eq_bot_of_isBender hBender)
  · exact center_ne_bot_of_isTwoAlt hK₁alt (center_eq_bot_of_isBender hBender)
  · exact center_ne_bot_of_isTwoSz8 hSz (center_eq_bot_of_isBender hBender)

end Core

theorem prop212 (hKI6 : K.KI6) :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (M : Subgroup G) (z : G), Hyp21 S M z →
      centralizer ({z} : Set G) ≤ M →
        IsInvariantInvolutionSet {g : G | IsConj z g} ∧ IsProductDisconnected {g : G | IsConj z g} M := by
  intro G _ _ S M z h hHM
  have hz2 : orderOf z = 2 := h.z_invol
  have hrank2 : 2 ≤ Open.pRank 2 (S : Subgroup G) := le_trans (by norm_num) h.rank
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_self z
  refine ⟨⟨fun g hg => orderOf_eq_two_of_isConj hz2 hg, fun g hg c => ?_⟩, ?_⟩
  · exact IsConj.trans hg (isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]⟩)
  · refine ⟨h.maximal.1, ⟨z, IsConj.refl z, hHM hzH⟩, ?_, ?_⟩
    · intro z' hz' hz'M g
      have hz'c : IsConj z z' := hz'
      constructor
      · intro hg
        have hz'2 := orderOf_eq_two_of_isConj hz2 hz'c
        obtain ⟨m, hmM, hm⟩ := controls_involution_fusion S hrank2 h.gamma_le hz'2 hz'M hg
        have hcz : g * m⁻¹ ∈ centralizer ({z'} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc g * m⁻¹ * z' = g * (m⁻¹ * z' * m) * m⁻¹ := by group
            _ = g * (g⁻¹ * z' * g) * m⁻¹ := by rw [hm]
            _ = z' * (g * m⁻¹) := by group
        have hgm := centralizer_le_of_conj h hHM hz'c hz'M hcz
        have h2 : g = (g * m⁻¹) * m := by group
        rw [h2]
        exact M.mul_mem hgm hmM
      · intro hg
        exact M.mul_mem (M.mul_mem (M.inv_mem hg) hz'M) hg
    · rintro u ⟨hu2, x, hx, y, hy, hxy, hu⟩ huM
      have hxc : IsConj z x := hx
      have hyc : IsConj z y := hy
      obtain ⟨m, hmM, hmS, hext⟩ := exists_extremal_mem h hu2 huM
      have hu'2 : orderOf (m⁻¹ * u * m) = 2 := by
        simpa [hu2] using (MulAut.conj m⁻¹).orderOf_eq u
      have hxy' : (m⁻¹ * x * m) * (m⁻¹ * y * m) = (m⁻¹ * y * m) * (m⁻¹ * x * m) := by
        calc (m⁻¹ * x * m) * (m⁻¹ * y * m) = m⁻¹ * (x * y) * m := by group
          _ = m⁻¹ * (y * x) * m := by rw [hxy]
          _ = (m⁻¹ * y * m) * (m⁻¹ * x * m) := by group
      have hu' : m⁻¹ * u * m = (m⁻¹ * x * m) * (m⁻¹ * y * m) := by
        rw [hu]
        group
      have hcore := core212 hKI6 h hHM hu'2 hmS hext (x := m⁻¹ * x * m) (y := m⁻¹ * y * m)
        (IsConj.trans hxc (isConj_iff.mpr ⟨m⁻¹, by rw [inv_inv]⟩))
        (IsConj.trans hyc (isConj_iff.mpr ⟨m⁻¹, by rw [inv_inv]⟩)) hxy' hu'
      intro g hg
      have hg := Subgroup.mem_centralizer_singleton_iff.mp hg
      have hg' : m⁻¹ * g * m ∈ centralizer ({m⁻¹ * u * m} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc m⁻¹ * g * m * (m⁻¹ * u * m) = m⁻¹ * (g * u) * m := by group
          _ = m⁻¹ * (u * g) * m := by rw [hg]
          _ = m⁻¹ * u * m * (m⁻¹ * g * m) := by group
      have h3 := M.mul_mem (M.mul_mem hmM (hcore hg')) (M.inv_mem hmM)
      have h4 : m * (m⁻¹ * g * m) * m⁻¹ = g := by group
      rw [h4] at h3
      exact h3

theorem cor213 (hKI6 : K.KI6) (hCorZD : S_CorZD) : Cor213Stmt := by
  intro G _ _ S M z h hHM
  obtain ⟨hinv, hpd⟩ := prop212 hKI6 G S M z h hHM
  exact (hCorZD G h.simple h.nonab {g : G | IsConj z g} M hinv hpd).1

end CFSG.GH74.Uniqueness.SU.SU10
