module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7C_Split

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM

namespace A7Comm

section A7CommAux

variable {V : Type} [Group V] {Kh : Subgroup (MulAut V)} {Y : Subgroup V}

@[expose] def commIn (Kh : Subgroup (MulAut V)) (Y : Subgroup V) : Subgroup V :=
  Subgroup.closure {c | ∃ g ∈ Kh, ∃ y ∈ Y, c = g y * y⁻¹}

theorem commV'_eq_commIn (Kh : Subgroup (MulAut V)) : commV' Kh = commIn Kh ⊤ := by
  unfold commV' commIn
  congr 1
  ext c
  simp

theorem commIn_le (hY : ∀ g ∈ Kh, ∀ y ∈ Y, g y ∈ Y) : commIn Kh Y ≤ Y := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g, hg, y, hy, rfl⟩
  exact Y.mul_mem (hY g hg y hy) (Y.inv_mem hy)

theorem commIn_inv (hY : ∀ g ∈ Kh, ∀ y ∈ Y, g y ∈ Y) :
    ∀ h ∈ Kh, ∀ c ∈ commIn Kh Y, h c ∈ commIn Kh Y := by
  intro h hh c hc
  have key : commIn Kh Y ≤ (commIn Kh Y).comap (h : MulAut V).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, hg, y, hy, rfl⟩
    refine Subgroup.subset_closure ⟨h * g * h⁻¹, Kh.mul_mem (Kh.mul_mem hh hg) (Kh.inv_mem hh),
      h y, hY h hh y hy, ?_⟩
    simp [MulAut.mul_apply]
  exact key hc

theorem commutator_eq_top_of_perf (hperf : ⁅Kh, Kh⁆ = Kh) : commutator ↥Kh = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have h1 : (g : MulAut V) ∈ (commutator ↥Kh).map Kh.subtype := by
    rw [Subgroup.map_subtype_commutator, hperf]
    exact g.2
  obtain ⟨x, hx, hxg⟩ := h1
  have : x = g := Subtype.ext hxg
  exact this ▸ hx

theorem aux_id (hc : ∀ a b : V, a * b = b * a) (gb a b y : V) :
    gb * y⁻¹ = (gb * a⁻¹ * (b * y⁻¹)⁻¹) * ((a * y⁻¹) * (b * y⁻¹)) := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hc }
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem commIn_commIn (hperf : ⁅Kh, Kh⁆ = Kh) (hc : ∀ a b : V, a * b = b * a)
    (hY : ∀ g ∈ Kh, ∀ y ∈ Y, g y ∈ Y) : commIn Kh (commIn Kh Y) = commIn Kh Y := by
  have hR := commIn_inv hY
  refine le_antisymm (commIn_le hR) ?_
  haveI : IsMulCommutative V := IsMulCommutative.of_comm hc
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g₀, hg₀, y, hy, rfl⟩
  let W₂ : Subgroup V := commIn Kh (commIn Kh Y)
  let f : ↥Kh →* V ⧸ W₂ :=
    { toFun := fun g => QuotientGroup.mk ((g : MulAut V) y * y⁻¹)
      map_one' := by simp
      map_mul' := fun g g' => by
        have hu : (g' : MulAut V) y * y⁻¹ ∈ commIn Kh Y :=
          Subgroup.subset_closure ⟨g', g'.2, y, hy, rfl⟩
        have hw : (g : MulAut V) ((g' : MulAut V) y * y⁻¹) * ((g' : MulAut V) y * y⁻¹)⁻¹ ∈ W₂ :=
          Subgroup.subset_closure ⟨g, g.2, _, hu, rfl⟩
        have hid : ((g * g' : ↥Kh) : MulAut V) y * y⁻¹ =
            ((g : MulAut V) ((g' : MulAut V) y * y⁻¹) * ((g' : MulAut V) y * y⁻¹)⁻¹) *
              (((g : MulAut V) y * y⁻¹) * ((g' : MulAut V) y * y⁻¹)) := by
          simp only [map_mul, map_inv, Subgroup.coe_mul, MulAut.mul_apply]
          exact aux_id hc _ _ _ _
        show QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
        rw [hid, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hw, one_mul,
          QuotientGroup.mk_mul] }
  haveI : IsMulCommutative (V ⧸ W₂) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.2
      (by rw [(commutator_eq_bot_iff V).2 inferInstance]; exact bot_le)
  have hker : ∀ g : ↥Kh, f g = 1 := by
    intro g
    have h1 := Abelianization.commutator_subset_ker f
    rw [commutator_eq_top_of_perf hperf] at h1
    exact h1 (Subgroup.mem_top g)
  exact (QuotientGroup.eq_one_iff _).1 (hker ⟨g₀, hg₀⟩)

@[expose] def actOn (Kh : Subgroup (MulAut V)) {R : Subgroup V} (hR : ∀ g ∈ Kh, ∀ r ∈ R, g r ∈ R) :
    ↥Kh →* MulAut ↥R where
  toFun g :=
    { toFun := fun u => ⟨(g : MulAut V) u, hR _ g.2 _ u.2⟩
      invFun := fun u => ⟨(g : MulAut V)⁻¹ u, hR _ (Kh.inv_mem g.2) _ u.2⟩
      left_inv := fun u => Subtype.ext ((g : MulAut V).symm_apply_apply (u : V))
      right_inv := fun u => Subtype.ext ((g : MulAut V).apply_symm_apply (u : V))
      map_mul' := fun u w => Subtype.ext (map_mul (g : MulAut V) (u : V) w) }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

end A7CommAux

section A7CommCore

variable {V : Type} [Group V] [Finite V] {Kh : Subgroup (MulAut V)}

open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.QuasithinUnique.L246.C123 in
theorem a7Comm_core
    (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    {π7 : ↥Kh →* ↥(alternatingGroup (Fin 7))} (hπ : Function.Surjective π7)
    (hker : ∀ q : ↥Kh, π7 q = 1 → q = 1)
    {R : Subgroup V} (hR : ∀ g ∈ Kh, ∀ r ∈ R, g r ∈ R) (hRc : commIn Kh R = R) (hRne : R ≠ ⊥) :
    16 * Nat.card ↥(R ⊓ fixV' Kh) ≤ Nat.card ↥R ∧
      (Nat.card ↥R = 16 * Nat.card ↥(R ⊓ fixV' Kh) → R ⊓ fixV' Kh = ⊥) := by
  haveI : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).2 hRne
  letI : CommGroup ↥R :=
    { (inferInstance : Group ↥R) with mul_comm := fun a b => Subtype.ext (hc _ _) }
  let act : ↥Kh →* MulAut ↥R := actOn Kh hR
  have hV2 : ∀ v : ↥R, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [pow_two] using h2 v)
  have hkerα : ∀ q : ↥Kh, π7 q = 1 → act q = 1 := fun q hq => by rw [hker q hq, map_one]
  let Z : Subgroup ↥R := (R ⊓ fixV' Kh).subgroupOf R
  have hZfix : ∀ g : ↥Kh, ∀ z ∈ Z, act g z = z := by
    intro g z hz
    have hz' : (z : V) ∈ fixV' Kh := (Subgroup.mem_subgroupOf.1 hz).2
    exact Subtype.ext (hz' g g.2)
  have hgen : Subgroup.closure {x : ↥R | ∃ (g : ↥Kh) (v : ↥R), x = act g v * v⁻¹} = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hu : (u : V) ∈ commIn Kh R := by rw [hRc]; exact u.2
    have hmap : (Subgroup.closure {x : ↥R | ∃ (g : ↥Kh) (v : ↥R), x = act g v * v⁻¹}).map
        R.subtype = commIn Kh R := by
      rw [MonoidHom.map_closure]
      unfold commIn
      congr 1
      ext c
      constructor
      · rintro ⟨x, ⟨g, v, rfl⟩, rfl⟩
        exact ⟨g, g.2, v, v.2, rfl⟩
      · rintro ⟨g, hg, y, hy, rfl⟩
        exact ⟨act ⟨g, hg⟩ ⟨y, hy⟩ * (⟨y, hy⟩ : ↥R)⁻¹, ⟨⟨g, hg⟩, ⟨y, hy⟩, rfl⟩, rfl⟩
    rw [← hmap] at hu
    obtain ⟨s, hs, hsu⟩ := hu
    have : s = u := Subtype.ext hsu
    exact this ▸ hs
  have hZcard : Nat.card Z = Nat.card ↥(R ⊓ fixV' Kh) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  refine ⟨?_, fun hcard => ?_⟩
  · have h := a7h_sixteen_mul_card_le hV2 act π7 hπ hkerα Z hZfix hgen
    rwa [hZcard] at h
  · have hcard' : Nat.card ↥R = 16 * Nat.card Z := by rw [hZcard]; exact hcard
    have hZ := central_zero_abstract hV2 act π7 hπ hkerα Z hZfix hcard' hgen
    rw [← Subgroup.card_eq_one, ← hZcard, hZ, Subgroup.card_bot]

end A7CommCore

end A7Comm

open A7Comm

variable {V : Type} [Group V] [Finite V]
variable {Kh Eh : Subgroup (MulAut V)}

theorem a7_comm_irred_aux
    (hc : ∀ a b : V, a * b = b * a) (h2 : ∀ v : V, v * v = 1)
    {π7 : ↥Kh →* ↥(alternatingGroup (Fin 7))} {Vv7 V₇ : Subgroup ↥(alternatingGroup (Fin 7))}
    (d : ASData Kh Eh 7 π7 Vv7 V₇) (hZ : Subgroup.center ↥Kh = ⊥) (hidx : (fixV' Kh).index = 16) :
    Nat.card ↥(commV' Kh) = 16 ∧ ∀ Y : Subgroup V, Y ≤ commV' Kh → (∀ g ∈ Kh, ∀ y ∈ Y, g y ∈ Y) →
      Y = ⊥ ∨ Y = commV' Kh := by
  have hker : ∀ q : ↥Kh, π7 q = 1 → q = 1 := by
    intro q hq
    have h : q ∈ π7.ker := hq
    rw [d.ker, hZ, Subgroup.mem_bot] at h
    exact h
  have hperf := d.perf
  have htop : ∀ g ∈ Kh, ∀ y ∈ (⊤ : Subgroup V), g y ∈ (⊤ : Subgroup V) := fun _ _ _ _ => trivial
  have hUinv : ∀ g ∈ Kh, ∀ y ∈ commV' Kh, g y ∈ commV' Kh := by
    rw [commV'_eq_commIn]
    exact commIn_inv htop
  have hUc : commIn Kh (commV' Kh) = commV' Kh := by
    rw [commV'_eq_commIn]
    exact commIn_commIn hperf hc htop
  have hUne : commV' Kh ≠ ⊥ := by
    intro hbot
    have hfix : fixV' Kh = ⊤ := by
      rw [eq_top_iff]
      intro v _ g hg
      have h1 : g v * v⁻¹ ∈ commV' Kh := Subgroup.subset_closure ⟨g, hg, v, rfl⟩
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
    rw [hfix, Subgroup.index_top] at hidx
    omega
  obtain ⟨hlow, hzero⟩ := a7Comm_core hc h2 d.surj hker hUinv hUc hUne
  have hupper : Nat.card ↥(commV' Kh) ≤ 16 * Nat.card ↥(commV' Kh ⊓ fixV' Kh) := by
    have h1 := Subgroup.relIndex_mul_card (fixV' Kh) (commV' Kh)
    have hne : (fixV' Kh).relIndex ⊤ ≠ 0 := by
      rw [Subgroup.relIndex_top_right, hidx]
      norm_num
    have h3 := Subgroup.relIndex_le_of_le_right (le_top : commV' Kh ≤ ⊤) hne
    rw [Subgroup.relIndex_top_right, hidx] at h3
    rw [inf_comm] at h1
    calc Nat.card ↥(commV' Kh) = (fixV' Kh).relIndex (commV' Kh) *
          Nat.card ↥(commV' Kh ⊓ fixV' Kh) := h1.symm
      _ ≤ 16 * Nat.card ↥(commV' Kh ⊓ fixV' Kh) := Nat.mul_le_mul_right _ h3
  have hUC0 : commV' Kh ⊓ fixV' Kh = ⊥ := hzero (le_antisymm hupper hlow)
  have hU16 : Nat.card ↥(commV' Kh) = 16 := by
    have h1 := le_antisymm hupper hlow
    rw [hUC0, Subgroup.card_bot] at h1
    omega
  refine ⟨hU16, ?_⟩
  intro Y hYU hYinv
  by_cases hY : Y = ⊥
  · exact Or.inl hY
  right
  have hRle : commIn Kh Y ≤ Y := commIn_le hYinv
  have hRinv := commIn_inv hYinv
  have hRc : commIn Kh (commIn Kh Y) = commIn Kh Y := commIn_commIn hperf hc hYinv
  have hRne : commIn Kh Y ≠ ⊥ := by
    intro hbot
    apply hY
    have hYfix : Y ≤ fixV' Kh := by
      intro y hy g hg
      have h1 : g y * y⁻¹ ∈ commIn Kh Y := Subgroup.subset_closure ⟨g, hg, y, hy, rfl⟩
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
    have h3 : Y ≤ commV' Kh ⊓ fixV' Kh := le_inf hYU hYfix
    rw [hUC0] at h3
    exact eq_bot_iff.2 h3
  have hK := (a7Comm_core hc h2 d.surj hker hRinv hRc hRne).1
  have hpos : 0 < Nat.card ↥(commIn Kh Y ⊓ fixV' Kh) := Nat.card_pos
  have h4 : Nat.card ↥(commIn Kh Y) ≤ Nat.card ↥Y := Subgroup.card_le_of_le hRle
  exact Subgroup.eq_of_le_of_card_ge hYU (by omega)

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM
