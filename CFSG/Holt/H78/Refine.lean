module

public import CFSG.Holt.H78.Equivalence
import CFSG.Holt.H78.DataSylow
import CFSG.Holt.H78.Lemma27SE
import CFSG.Holt.H78.OrbitalOdd
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

section Lines

theorem IsHoltFactor.exists_mem_apply_eq_apply_eq {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    {M : Subgroup (Equiv.Perm Δ)} (hM : IsHoltFactor M) {a b c : Δ} (hba : b ≠ a)
    (hca : c ≠ a) : ∃ m ∈ M, m a = a ∧ m b = c := by
  rcases hM with ⟨rfl, h7⟩ | hSE
  · exact exists_mem_alternatingGroup_fix_apply_eq (by omega) hba hca
  · obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hSE
    obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
    obtain ⟨p, hp, hpb⟩ := hA.exists_mem_smul_eq hQ hba hca
    exact ⟨p, p.2, hQ hp, hpb⟩

theorem HoltData.exists_mem_jHull_smul_eq {X Δ : Type*} [Group X] [MulAction X Δ]
    (D : HoltData X Δ) (hO : jOddCore X Δ = ⊥) {i : D.ι} {a b c : Δ}
    (hb : ∀ j, j ≠ i → D.coord b j = D.coord a j) (hc : ∀ j, j ≠ i → D.coord c j = D.coord a j)
    (hba : b ≠ a) (hca : c ≠ a) : ∃ h ∈ jHull X Δ, h • a = a ∧ h • b = c := by
  have hne : ∀ {x : Δ}, (∀ j, j ≠ i → D.coord x j = D.coord a j) → x ≠ a →
      D.coord x i ≠ D.coord a i := fun {x} hx hxa h => hxa (HoltData.coord_injective (D := D) hO
    (funext fun j => if hj : j = i then hj ▸ h else hx j hj))
  obtain ⟨m, hm, hma, hmb⟩ := (D.factor i).exists_mem_apply_eq_apply_eq (hne hb hba) (hne hc hca)
  obtain ⟨l, hl, hlm⟩ := HoltData.mem_M.mp hm
  have hcoord : ∀ x : Δ, ∀ j, j ≠ i → D.coord ((l : X) • x) j = D.coord x j := fun x j hj => by
    rw [D.coord_smul, HoltData.rho_eq_one_of_mem_L (Ne.symm hj) hl, Equiv.Perm.one_apply]
  refine ⟨l, l.2, HoltData.coord_injective (D := D) hO (funext fun j => ?_),
    HoltData.coord_injective (D := D) hO (funext fun j => ?_)⟩
  · by_cases hj : j = i
    · subst hj
      rw [D.coord_smul, hlm, hma]
    · exact hcoord a j hj
  · by_cases hj : j = i
    · subst hj
      rw [D.coord_smul, hlm, hmb]
    · rw [hcoord b j hj, hb j hj, hc j hj]

theorem HoltData.coord_smul_of_mem_L {X Δ : Type*} [Group X] [MulAction X Δ]
    (D : HoltData X Δ) {i : D.ι} (l : D.L i) (x : Δ) {j : D.ι} (hj : j ≠ i) :
    D.coord (l • x) j = D.coord x j := by
  have := D.coord_smul ⟨l, D.L_le i l.2⟩ x j
  rw [HoltData.rho_eq_one_of_mem_L (Ne.symm hj) l.2, Equiv.Perm.one_apply] at this
  exact this

end Lines

section Lemma35i

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]

omit [Finite G] [Finite Ω] in
theorem card_longInvSwap_smul_right {α β : Ω} {h : G} (hh : h ∈ stabilizer G α) :
    Nat.card (longInvSwap G Ω α (h • β)) = Nat.card (longInvSwap G Ω α β) := by
  have hhα : h • α = α := hh
  have e := conj_longInvSwap h α β
  rw [hhα] at e
  rw [← e]
  exact Nat.card_image_of_injective (fun x y hxy => by simpa using hxy) _

theorem mem_orbit_of_mem_fixSet_sylow {v : G} (hv : orderOf v = 2)
    (D : HoltData ↥(typeLSection G Ω v) ↥(fixSet Ω (Subgroup.zpowers v)))
    (hO : jOddCore ↥(typeLSection G Ω v) ↥(fixSet Ω (Subgroup.zpowers v)) = ⊥) {i : D.ι}
    {a b : fixSet Ω (Subgroup.zpowers v)} (hab : ∀ j, j ≠ i → D.coord b j = D.coord a j)
    (hba : b ≠ a) {S : Subgroup G}
    (hS : fusionIsSylowIn 2 S (stabilizer G (a : Ω) ⊓ stabilizer G (b : Ω))) {ω : Ω}
    (hω : ω ∈ fixSet Ω S) (hωa : ω ≠ a) : ω ∈ orbit (stabilizer G (a : Ω)) (b : Ω) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := isPGroup_zpowers_of_orderOf_eq_two hv
  have hline : ∀ c : fixSet Ω (Subgroup.zpowers v), c ∈ orbit (D.L i) a → c ≠ a →
      (c : Ω) ∈ orbit (stabilizer G (a : Ω)) (b : Ω) := by
    intro c hc hca
    obtain ⟨l, rfl⟩ := hc
    obtain ⟨h, -, hha, hhb⟩ := D.exists_mem_jHull_smul_eq hO hab
      (fun j hj => D.coord_smul_of_mem_L l a hj) hba hca
    obtain ⟨x, -, hxh⟩ := mem_centralizerImage.mp h.2
    refine ⟨⟨x, ?_⟩, ?_⟩
    · exact (hxh a).symm.trans (congrArg Subtype.val hha)
    · exact (hxh b).symm.trans (congrArg Subtype.val hhb)
  obtain ⟨P, -, hP⟩ := exists_fusionIsSylowIn_ge (p := 2) IsPGroup.of_bot
    (bot_le : ⊥ ≤ stabilizer (typeLSection G Ω v) a ⊓ stabilizer (typeLSection G Ω v) b)
  have hK3 := HoltData.fixSet_sylow_twoPoint (D := D) hO hab hP
  obtain ⟨R, hRC, hR, hlift, hlift'⟩ := exists_isPGroup_lift_inducedPerm
    (X := Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (Δ := fixSet Ω (Subgroup.zpowers v)) (hX := centralizer_le_stabilizer_fixSet _) (R := P)
    hP.2.1
  have hRab : R ≤ stabilizer G (a : Ω) ⊓ stabilizer G (b : Ω) := fun r hr => by
    obtain ⟨y, hy, hyr⟩ := hlift r hr
    have h1 := mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hP.1 hy)).1
    have h2 := mem_stabilizer_iff.mp (Subgroup.mem_inf.mp (hP.1 hy)).2
    exact Subgroup.mem_inf.mpr ⟨(hyr a).symm.trans (congrArg Subtype.val h1),
      (hyr b).symm.trans (congrArg Subtype.val h2)⟩
  have hvab : Subgroup.zpowers v ≤ stabilizer G (a : Ω) ⊓ stabilizer G (b : Ω) :=
    le_inf (mem_fixSet_iff_le_stabilizer.mp a.2) (mem_fixSet_iff_le_stabilizer.mp b.2)
  have hRN : R ≤ Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    hRC.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨S₀, hES₀, hS₀⟩ := exists_fusionIsSylowIn_ge (hR.to_sup_of_normal_right' hv2 hRN)
    (sup_le hRab hvab)
  have hfix₀ : ∀ ω ∈ fixSet Ω S₀, ω ≠ a → ω ∈ orbit (stabilizer G (a : Ω)) (b : Ω) := by
    intro ω hω hωa
    have hωF : ω ∈ fixSet Ω (Subgroup.zpowers v) := fun x hx =>
      hω x (hES₀ (Subgroup.mem_sup_right hx))
    refine hline ⟨ω, hωF⟩ (hK3 fun y hy => ?_) (fun h => hωa (congrArg Subtype.val h))
    obtain ⟨r, hr, hry⟩ := hlift' y hy
    exact Subtype.ext ((hry ⟨ω, hωF⟩).trans (hω r (hES₀ (Subgroup.mem_sup_left hr))))
  obtain ⟨k, hk, hkS⟩ := exists_map_conj_eq_of_fusionIsSylowIn hS₀ hS
  have hka : k • (a : Ω) = a := (Subgroup.mem_inf.mp hk).1
  have hk' : k⁻¹ • ω ∈ fixSet Ω S₀ := fun s hs => by
    have := hω (k * s * k⁻¹) (hkS ▸ ⟨s, hs, rfl⟩)
    rw [mul_smul, mul_smul] at this
    exact (smul_eq_iff_eq_inv_smul k).mp this
  have hk'a : k⁻¹ • ω ≠ a := fun h => hωa (calc ω = k • k⁻¹ • ω := (smul_inv_smul k ω).symm
    _ = k • (a : Ω) := by rw [h]
    _ = a := hka)
  obtain ⟨⟨x, hx⟩, hxb⟩ := hfix₀ _ hk' hk'a
  refine ⟨⟨k * x, mul_mem (Subgroup.mem_inf.mp hk).1 hx⟩, ?_⟩
  show (k * x) • (b : Ω) = ω
  rw [mul_smul]
  have hxb' : x • (b : Ω) = k⁻¹ • ω := hxb
  rw [hxb', smul_inv_smul]

theorem lemma_3_5_i (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {v : G} (hv : orderOf v = 2)
    (D : HoltData ↥(typeLSection G Ω v) ↥(fixSet Ω (Subgroup.zpowers v)))
    (hO : jOddCore ↥(typeLSection G Ω v) ↥(fixSet Ω (Subgroup.zpowers v)) = ⊥) {i : D.ι}
    {a b : fixSet Ω (Subgroup.zpowers v)} (hab : ∀ j, j ≠ i → D.coord b j = D.coord a j) :
    Nat.card (longInvSwap G Ω a b) = Nat.card (longInvAt G Ω a) := by
  classical
  have := Fintype.ofFinite Ω
  by_cases hba : b = a
  · rw [hba, longInvSwap_self]
  have hba' : (b : Ω) ≠ a := fun h => hba (Subtype.ext h)
  set Λ : Finset Ω := Finset.univ.filter fun ω => ω ∈ orbit (stabilizer G (a : Ω)) (b : Ω)
    with hΛdef
  have hmem : ∀ ω, ω ∈ Λ ↔ ω ∈ orbit (stabilizer G (a : Ω)) (b : Ω) := fun ω => by
    simp [hΛdef]
  have hΛα : ∀ β ∈ Λ, β ≠ (a : Ω) := by
    intro β hβ h
    obtain ⟨⟨g, hg⟩, hgb⟩ := (hmem β).mp hβ
    have hgb' : g • (b : Ω) = g • (a : Ω) := by
      rw [mem_stabilizer_iff.mp hg]
      exact hgb.trans h
    exact hba' (smul_left_cancel g hgb')
  have hΛ : ∀ β ∈ Λ, ∀ γ, γ ≠ (a : Ω) → HoltSim G Ω a β γ → γ ∈ Λ := by
    intro β hβ γ hγa hsim
    obtain ⟨⟨h, hh⟩, rfl⟩ := (hmem β).mp hβ
    obtain ⟨g, hg, S, hS, hS'⟩ := (holtSim_smul_left_iff hh).mp hsim
    have hgγ : g • γ ∈ fixSet Ω S :=
      mem_fixSet_iff_le_stabilizer.mpr (hS'.1.trans inf_le_right)
    have hgγa : g • γ ≠ (a : Ω) := fun h' => hγa (smul_left_cancel g
      (h'.trans (mem_stabilizer_iff.mp hg).symm))
    obtain ⟨⟨x, hx⟩, hxb⟩ := mem_orbit_of_mem_fixSet_sylow hv D hO hab hba hS hgγ hgγa
    rw [hmem]
    refine ⟨⟨g⁻¹ * x, mul_mem (inv_mem hg) hx⟩, ?_⟩
    show (g⁻¹ * x) • (b : Ω) = γ
    have hxb' : x • (b : Ω) = g • γ := hxb
    rw [mul_smul, hxb', inv_smul_smul]
  have h33 := lemma_3_3_i hG hB hΛα hΛ
  have hconst : ∀ β ∈ Λ, Nat.card (longInvSwap G Ω a β) = Nat.card (longInvSwap G Ω a b) := by
    intro β hβ
    obtain ⟨⟨h, hh⟩, rfl⟩ := (hmem β).mp hβ
    exact card_longInvSwap_smul_right hh
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at h33
  have hpos : 0 < Λ.card := Finset.card_pos.mpr ⟨b, (hmem b).mpr (mem_orbit_self _)⟩
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h33, mul_comm])

end Lemma35i

section Nabla

variable (G : Type) [Group G] (Ω : Type) [MulAction G Ω]

@[expose] def typeLOrbit (v : G) (P : Subgroup (typeLSection G Ω v)) (α : Ω) : Set Ω :=
  {ω | ∃ p ∈ P, ∃ a : fixSet Ω (Subgroup.zpowers v), (a : Ω) = α ∧ ((p • a : _) : Ω) = ω}

@[expose] def holtNabla (v : G) (P : Subgroup (typeLSection G Ω v)) (α : Ω) : Set Ω :=
  {ω | ∃ g ∈ stabilizer G α, ∃ β ∈ typeLOrbit G Ω v P α, β ≠ α ∧ g • β = ω}

variable {G Ω}

theorem typeLOrbit_subset {v : G} {P : Subgroup (typeLSection G Ω v)} {α : Ω} :
    typeLOrbit G Ω v P α ⊆ fixSet Ω (Subgroup.zpowers v) := by
  rintro _ ⟨p, -, a, -, rfl⟩
  exact (p • a).2

theorem mem_fixSet_of_mem_typeLOrbit {v : G} {P : Subgroup (typeLSection G Ω v)} {α ω : Ω}
    (hω : ω ∈ typeLOrbit G Ω v P α) : α ∈ fixSet Ω (Subgroup.zpowers v) := by
  obtain ⟨-, -, a, rfl, -⟩ := hω
  exact a.2

theorem mem_typeLOrbit_self {v : G} {P : Subgroup (typeLSection G Ω v)} {α : Ω}
    (hα : α ∈ fixSet Ω (Subgroup.zpowers v)) : α ∈ typeLOrbit G Ω v P α :=
  ⟨1, one_mem _, ⟨α, hα⟩, rfl, by rw [one_smul]⟩

theorem smul_mem_typeLOrbit {v : G} {P : Subgroup (typeLSection G Ω v)} (hPn : P.Normal)
    {α : Ω} {c : G} (hc : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    {x : Ω} (hx : x ∈ typeLOrbit G Ω v P α) (hcx : c • x ∈ typeLOrbit G Ω v P α) {y : Ω}
    (hy : y ∈ typeLOrbit G Ω v P α) : c • y ∈ typeLOrbit G Ω v P α := by
  obtain ⟨p₁, hp₁, a, rfl, rfl⟩ := hx
  obtain ⟨p₃, hp₃, a', ha', hp₃a⟩ := hcx
  obtain ⟨p₂, hp₂, a'', ha'', rfl⟩ := hy
  obtain rfl : a' = a := Subtype.ext ha'
  obtain rfl : a'' = a' := Subtype.ext ha''
  set c' : typeLSection G Ω v :=
    ⟨MulAction.toPermHom _ _ (⟨c, hc⟩ : Subgroup.centralizer _), ⟨c, hc⟩, rfl⟩ with hc'
  have hc'δ : ∀ δ : fixSet Ω (Subgroup.zpowers v),
      ((c' • δ : fixSet Ω (Subgroup.zpowers v)) : Ω) = c • (δ : Ω) := fun δ => rfl
  have e3 : p₃ • a'' = c' • p₁ • a'' := Subtype.ext (hp₃a.trans (hc'δ _).symm)
  refine ⟨c' * (p₂ * p₁⁻¹) * c'⁻¹ * p₃,
    mul_mem (hPn.conj_mem _ (mul_mem hp₂ (inv_mem hp₁)) c') hp₃, a'', rfl, ?_⟩
  rw [← hc'δ]
  congr 1
  rw [mul_smul, e3, smul_smul, smul_smul, smul_smul]
  congr 1
  group

theorem odd_card_typeLOrbit {v : G} {P : Subgroup (typeLSection G Ω v)}
    (hPodd : Odd (Nat.card P)) {α : Ω} (hα : α ∈ fixSet Ω (Subgroup.zpowers v)) :
    Odd (Nat.card (typeLOrbit G Ω v P α)) := by
  have he : typeLOrbit G Ω v P α =
      Subtype.val '' orbit P (⟨α, hα⟩ : fixSet Ω (Subgroup.zpowers v)) := by
    ext ω
    constructor
    · rintro ⟨p, hp, a, ha, rfl⟩
      obtain rfl : a = ⟨α, hα⟩ := Subtype.ext ha
      exact ⟨(⟨p, hp⟩ : P) • (⟨α, hα⟩ : fixSet Ω (Subgroup.zpowers v)), ⟨⟨p, hp⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨⟨p, hp⟩, rfl⟩, rfl⟩
      exact ⟨p, hp, ⟨α, hα⟩, rfl, rfl⟩
  rw [he, Nat.card_image_of_injective Subtype.val_injective, Nat.card_coe_set_eq,
    ← index_stabilizer]
  exact Odd.of_dvd_nat hPodd (Subgroup.index_dvd_card _)

theorem smul_mem_holtNabla {v : G} {P : Subgroup (typeLSection G Ω v)} {α ω : Ω} {h : G}
    (hh : h ∈ stabilizer G α) (hω : ω ∈ holtNabla G Ω v P α) : h • ω ∈ holtNabla G Ω v P α := by
  obtain ⟨g, hg, β, hβ, hβα, rfl⟩ := hω
  exact ⟨h * g, mul_mem hh hg, β, hβ, hβα, mul_smul h g β⟩

theorem ne_of_mem_holtNabla {v : G} {P : Subgroup (typeLSection G Ω v)} {α ω : Ω}
    (hω : ω ∈ holtNabla G Ω v P α) : ω ≠ α := by
  obtain ⟨g, hg, β, -, hβα, rfl⟩ := hω
  intro h
  apply hβα
  have : g • β = g • α := h.trans (mem_stabilizer_iff.mp hg).symm
  exact smul_left_cancel g this

end Nabla

section Closures

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]

theorem mem_holtNabla_of_mem_holtDelta (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {v : G} (hv : orderOf v = 2)
    {P : Subgroup (typeLSection G Ω v)} (hPn : P.Normal) (hPodd : Odd (Nat.card P))
    {α β γ : Ω} (hβ : β ∈ holtNabla G Ω v P α) (hγ : γ ∈ holtDelta G Ω α β) :
    γ ∈ holtNabla G Ω v P α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh, β₀, hβ₀, hβ₀α, rfl⟩ := hβ
  have hhα : h • α = α := hh
  have hh'α : h⁻¹ • α = α := by rw [inv_smul_eq_iff, hhα]
  have hγ₀ : h⁻¹ • γ ∈ holtDelta G Ω α β₀ := by
    have := Set.smul_mem_smul_set (a := h⁻¹) hγ
    rwa [smul_holtDelta, hh'α, inv_smul_smul] at this
  suffices H : h⁻¹ • γ ∈ holtNabla G Ω v P α by
    have := smul_mem_holtNabla hh H
    rwa [smul_inv_smul] at this
  have hαF := mem_fixSet_of_mem_typeLOrbit hβ₀
  have hβ₀F := typeLOrbit_subset hβ₀
  have hαβ₀ : α ≠ β₀ := fun h' => hβ₀α h'.symm
  have hvab : Subgroup.zpowers v ≤ stabilizer G α ⊓ stabilizer G β₀ :=
    le_inf (mem_fixSet_iff_le_stabilizer.mp hαF) (mem_fixSet_iff_le_stabilizer.mp hβ₀F)
  obtain ⟨S, hvS, hS⟩ := exists_fusionIsSylowIn_ge (isPGroup_zpowers_of_orderOf_eq_two hv) hvab
  have hSΔ : S ≤ stabilizer G (holtDelta G Ω α β₀) :=
    hS.1.trans ((stabilizer_inf_le_stabilizer_pair α β₀).trans (stabilizer_pair_le α β₀))
  obtain ⟨γ', hγ'Δ, hγ'S⟩ :=
    exists_mem_fixSet_of_le_stabilizer hS.2.1 (hG.odd_card_holtDelta α β₀) hSΔ
  have hS' : fusionIsSylowIn 2 S (stabilizer G α ⊓ stabilizer G β₀ ⊓ stabilizer G γ') :=
    ⟨le_inf hS.1 (mem_fixSet_iff_le_stabilizer.mp hγ'S), hS.2.1,
      fun Q hQ hQ2 hSQ => hS.2.2 Q (hQ.trans inf_le_left) hQ2 hSQ⟩
  obtain ⟨-, u, hu, huγ', huS⟩ := lemma_3_2_i hG hB hαβ₀ hγ'Δ hS'
  have huC : u ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    Subgroup.centralizer_le hvS huS
  have hPO : ∀ y ∈ typeLOrbit G Ω v P α, u • y ∈ typeLOrbit G Ω v P α := fun y hy =>
    smul_mem_typeLOrbit hPn huC (mem_typeLOrbit_self hαF) (by rw [hu.2]; exact hβ₀) hy
  have hustab : Subgroup.zpowers u ≤ stabilizer G (typeLOrbit G Ω v P α) := by
    rw [Subgroup.zpowers_le, mem_stabilizer_set]
    intro y
    refine ⟨fun h' => ?_, hPO y⟩
    have := hPO _ h'
    rwa [← mul_smul, mul_self_eq_one_of_mem_longInv hu.1, one_smul] at this
  obtain ⟨θ, hθ, hθu⟩ := exists_mem_fixSet_of_le_stabilizer
    (isPGroup_zpowers_of_orderOf_eq_two hu.1.1) (odd_card_typeLOrbit hPodd hαF) hustab
  have hθγ' : θ = γ' :=
    (smul_eq_iff_of_mem_longInvAt ⟨hu.1, huγ'⟩ θ).mp (hθu u (Subgroup.mem_zpowers u))
  rw [hθγ'] at hθ
  have hγ'α : γ' ≠ α := fun h' => left_notMem_holtDelta hαβ₀ (h' ▸ hγ'Δ)
  rw [holtDelta_eq_orbit_of_mem hγ'Δ] at hγ₀
  obtain ⟨⟨k, hk⟩, hkθ⟩ := hγ₀
  exact ⟨k, (Subgroup.mem_inf.mp hk).1, γ', hθ, hγ'α, hkθ⟩

theorem mem_holtNabla_of_mem_holtDelta_of_mem
    (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {v : G}
    (hv : orderOf v = 2) {P : Subgroup (typeLSection G Ω v)} (hPn : P.Normal) {α β γ : Ω}
    (hγ : γ ∈ holtDelta G Ω α β) (hγN : γ ∈ holtNabla G Ω v P α) :
    β ∈ holtNabla G Ω v P α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh, γ₀, hγ₀, hγ₀α, rfl⟩ := hγN
  have hhα : h • α = α := hh
  have hh'α : h⁻¹ • α = α := by rw [inv_smul_eq_iff, hhα]
  have hγ₀Δ : γ₀ ∈ holtDelta G Ω α (h⁻¹ • β) := by
    have := Set.smul_mem_smul_set (a := h⁻¹) hγ
    rwa [smul_holtDelta, hh'α, inv_smul_smul] at this
  suffices H : h⁻¹ • β ∈ holtNabla G Ω v P α by
    have := smul_mem_holtNabla hh H
    rwa [smul_inv_smul] at this
  have hαF := mem_fixSet_of_mem_typeLOrbit hγ₀
  have hγ₀F := typeLOrbit_subset hγ₀
  obtain ⟨s, hs, hsγ₀⟩ := hγ₀Δ
  have hβ₀α : h⁻¹ • β ≠ α := fun h' =>
    hγ₀α ((smul_eq_iff_of_mem_longInvAt ⟨hs.1, hs.2.trans h'⟩ γ₀).mp hsγ₀)
  have hβ₀Δ' : h⁻¹ • β ∈ holtDelta' G Ω γ₀ α := ⟨s, ⟨hs.1, hsγ₀⟩, hs.2⟩
  have hvab : Subgroup.zpowers v ≤ stabilizer G γ₀ ⊓ stabilizer G α :=
    le_inf (mem_fixSet_iff_le_stabilizer.mp hγ₀F) (mem_fixSet_iff_le_stabilizer.mp hαF)
  obtain ⟨S, hvS, hS⟩ := exists_fusionIsSylowIn_ge (isPGroup_zpowers_of_orderOf_eq_two hv) hvab
  obtain ⟨u, hu, huS⟩ := lemma_3_3_iii_centralizer hG hB hγ₀α hS
  have huC := Subgroup.centralizer_le hvS huS
  have huα : u • α ∈ typeLOrbit G Ω v P α := smul_mem_typeLOrbit hPn huC hγ₀
    (by rw [hu.2]; exact hγ₀) (mem_typeLOrbit_self hαF)
  have huΔ' : u • α ∈ holtDelta' G Ω γ₀ α := ⟨u, hu, rfl⟩
  rw [lemma_3_3_iii_orbit hG hB hγ₀α hβ₀Δ'] at huΔ'
  obtain ⟨⟨k, hk⟩, hkβ⟩ := huΔ'
  have hkα : k • α = α := (Subgroup.mem_inf.mp hk).2
  have hkβ' : k • h⁻¹ • β = u • α := hkβ
  have hkN : k • h⁻¹ • β ∈ holtNabla G Ω v P α :=
    ⟨1, one_mem _, k • h⁻¹ • β, hkβ' ▸ huα,
      fun h' => hβ₀α (smul_left_cancel k (h'.trans hkα.symm)), one_smul G _⟩
  have := smul_mem_holtNabla (inv_mem (show k ∈ stabilizer G α from hkα)) hkN
  rwa [inv_smul_smul] at this

end Closures

section Lemma35ii

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]

theorem one_lt_card_holtDelta_of_le [FaithfulSMul G Ω] (hG : IsStarGroup G Ω)
    [IsPreprimitive G Ω] (hO : CFSG.pPrimeCore 2 G = ⊥) {α β : Ω} (hαβ : α ≠ β)
    (hm : Nat.card (longInvAt G Ω α) ≤ Nat.card (longInvSwap G Ω α β)) :
    1 < Nat.card (holtDelta G Ω α β) := by
  classical
  have := Fintype.ofFinite G
  have := hG.isPretransitive
  by_contra hlt
  have hle : Nat.card (holtDelta G Ω α β) ≤ 1 := not_lt.mp hlt
  obtain ⟨γ, hγ⟩ := holtDelta_nonempty hG α β
  have hΔ : ∀ δ ∈ holtDelta G Ω α β, δ = γ := fun δ hδ => by
    have : Subsingleton (holtDelta G Ω α β) := Finite.card_le_one_iff_subsingleton.mp hle
    exact congrArg Subtype.val (Subsingleton.elim (⟨δ, hδ⟩ : holtDelta G Ω α β) ⟨γ, hγ⟩)
  have hsub : longInvSwap G Ω α β ⊆ longInvAt G Ω γ := by
    intro s hs
    obtain ⟨θ, hθ⟩ := exists_mem_longInvAt hs.1
    have hθΔ : θ ∈ holtDelta G Ω α β := ⟨s, hs, hθ.2⟩
    rw [hΔ θ hθΔ] at hθ
    exact hθ
  have heq : longInvSwap G Ω α β = longInvAt G Ω γ := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hG.card_longInvAt_eq γ α]
    exact hm
  have hall : ∀ u ∈ longInvAt G Ω γ, u • α = β := fun u hu => by
    rw [← heq] at hu
    exact hu.2
  have hγα : γ ≠ α := fun h => left_notMem_holtDelta hαβ (h ▸ hγ)
  have hodd := lemma_3_4 hG (α := γ) (Γ := orbit ↥(stabilizer G γ) α)
    ⟨α, mem_orbit_self α, hγα.symm, rfl⟩
  have hfix : ∀ u ∈ longInvAt G Ω γ, ∀ w ∈ longInvAt G Ω γ,
      u * w ∈ stabilizer G γ ⊓ fixingSubgroup G (orbit ↥(stabilizer G γ) α) := by
    intro u hu w hw
    refine Subgroup.mem_inf.mpr ⟨by rw [mem_stabilizer_iff, mul_smul, hw.2, hu.2],
      (mem_fixingSubgroup_iff G).mpr ?_⟩
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    have hg' : g⁻¹ • γ = γ := by rw [inv_smul_eq_iff, mem_stabilizer_iff.mp hg]
    have key : ∀ x ∈ longInvAt G Ω γ, x • g • α = g • β := fun x hx => by
      have hx' := conj_mem_longInvAt hx g⁻¹
      rw [inv_inv, hg'] at hx'
      have := hall _ hx'
      rwa [mul_smul, mul_smul, inv_smul_eq_iff] at this
    show (u * w) • g • α = g • α
    rw [mul_smul, key w hw, ← key u hu, ← mul_smul, mul_self_eq_one_of_mem_longInv hu.1,
      one_smul]
  have hinv : ∀ u ∈ longInvAt G Ω γ, ∀ w ∈ longInvAt G Ω γ, u * w * (u * w) = 1 →
      u * w = 1 := fun u hu w hw h2 =>
    congrArg Subtype.val (eq_one_of_mul_self_eq_one_of_odd_card hodd
      (g := ⟨u * w, hfix u hu w hw⟩) (Subtype.ext h2))
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty γ
  have ht1 : t ≠ 1 := fun h => by
    have h2 := ht.1.1
    rw [h, orderOf_one] at h2
    omega
  have hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hc
    have hxJ : g * t * g⁻¹ ∈ longInv G Ω := conj_mem_longInv ht.1 g
    have hxγ : (g * t * g⁻¹) • γ = γ := by
      have h1 : t • (g * t * g⁻¹) • γ = (g * t * g⁻¹) • γ := by
        rw [← mul_smul, ← hc, mul_smul, ht.2]
      exact (smul_eq_iff_of_mem_longInvAt ht _).mp h1
    have h2 : (g * t * g⁻¹) * t * ((g * t * g⁻¹) * t) = 1 := by
      calc (g * t * g⁻¹) * t * ((g * t * g⁻¹) * t)
          = (g * t * g⁻¹) * (t * (g * t * g⁻¹)) * t := by group
        _ = (g * t * g⁻¹) * ((g * t * g⁻¹) * t) * t := by rw [← hc]
        _ = ((g * t * g⁻¹) * (g * t * g⁻¹)) * (t * t) := by group
        _ = 1 := by
          rw [mul_self_eq_one_of_mem_longInv hxJ, mul_self_eq_one_of_mem_longInv ht.1, one_mul]
    have h3 := hinv _ ⟨hxJ, hxγ⟩ t ht h2
    exact (eq_inv_of_mul_eq_one_left h3).trans (inv_eq_self_of_mem_longInv ht.1)
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G t ht1
    (mul_self_eq_one_of_mem_longInv ht.1) hiso
  have hNO : N ≤ CFSG.pPrimeCore 2 G := le_sSup ⟨hNn, Nat.coprime_two_left.mpr hNodd⟩
  rw [hO] at hNO
  have hcent : ∀ g : G, g * t = t * g := fun g => by
    have h1 := Subgroup.mem_bot.mp (hNO (hN g))
    calc g * t = (g * t * g⁻¹ * t⁻¹) * (t * g) := by group
      _ = t * g := by rw [h1, one_mul]
  obtain ⟨g, hg⟩ := exists_smul_eq G γ α
  have htα : t • α = α := by rw [← hg, ← mul_smul, ← hcent g, mul_smul, ht.2]
  exact hγα ((smul_eq_iff_of_mem_longInvAt ht α).mp htα).symm

theorem lemma_3_5_ii_sum (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω)) {v : G} (hv : orderOf v = 2)
    {P : Subgroup (typeLSection G Ω v)} (hPn : P.Normal) (hPodd : Odd (Nat.card P)) {α : Ω}
    {Λ : Finset Ω} (hΛα : ∀ β ∈ Λ, β ≠ α)
    (hΛ : ∀ β ∈ Λ, ∀ γ, γ ≠ α → HoltSim G Ω α β γ → γ ∈ Λ) {X : Finset Ω}
    (hX : ∀ β, β ∈ X ↔ β ∈ Λ ∧ β ∈ holtNabla G Ω v P α) :
    ∑ β ∈ X, Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α) * X.card := by
  classical
  set Y : Finset Ω := Λ.filter (· ∉ holtNabla G Ω v P α) with hYdef
  have hmemY : ∀ β, β ∈ Y ↔ β ∈ Λ ∧ β ∉ holtNabla G Ω v P α := fun β => by simp [hYdef]
  have hΛα' : ∀ β ∈ (Λ : Set Ω), β ≠ α := hΛα
  have hΛ' : ∀ β ∈ (Λ : Set Ω), ∀ γ, γ ≠ α → HoltSim G Ω α β γ → γ ∈ (Λ : Set Ω) := hΛ
  have hΛinv : ∀ h ∈ stabilizer G α, ∀ β ∈ Λ, h • β ∈ Λ := fun h hh β hβ =>
    smul_mem_of_holtSim_closed hΛα' hΛ' hh hβ
  have hΛΔ : ∀ β ∈ Λ, holtDelta G Ω α β ⊆ Λ := fun β hβ =>
    holtDelta_subset_of_holtSim_closed hG hB hΛα' hΛ' hβ
  have hXinv : ∀ h ∈ stabilizer G α, ∀ β ∈ X, h • β ∈ X := fun h hh β hβ => by
    rw [hX] at hβ ⊢
    exact ⟨hΛinv h hh β hβ.1, smul_mem_holtNabla hh hβ.2⟩
  have hXΔ : ∀ β ∈ X, holtDelta G Ω α β ⊆ X := fun β hβ γ hγ => by
    rw [hX] at hβ
    rw [Finset.mem_coe, hX]
    exact ⟨hΛΔ β hβ.1 hγ, mem_holtNabla_of_mem_holtDelta hG hB hv hPn hPodd hβ.2 hγ⟩
  have hYinv : ∀ h ∈ stabilizer G α, ∀ β ∈ Y, h • β ∈ Y := fun h hh β hβ => by
    rw [hmemY] at hβ ⊢
    refine ⟨hΛinv h hh β hβ.1, fun h' => hβ.2 ?_⟩
    have := smul_mem_holtNabla (inv_mem hh) h'
    rwa [inv_smul_smul] at this
  have hYΔ : ∀ β ∈ Y, holtDelta G Ω α β ⊆ Y := fun β hβ γ hγ => by
    rw [hmemY] at hβ
    rw [Finset.mem_coe, hmemY]
    exact ⟨hΛΔ β hβ.1 hγ, fun h' =>
      hβ.2 (mem_holtNabla_of_mem_holtDelta_of_mem hG hB hv hPn hγ h')⟩
  have hXle := sum_card_longInvSwap_le_of_holtDelta_subset hG hXinv hXΔ
  have hYle := sum_card_longInvSwap_le_of_holtDelta_subset hG hYinv hYΔ
  have hΛeq := lemma_3_3_i hG hB hΛα hΛ
  have hunion : Λ = X ∪ Y := by
    ext β
    rw [Finset.mem_union, hX, hmemY]
    tauto
  have hdisj : Disjoint X Y := Finset.disjoint_left.mpr fun β hβX hβY =>
    ((hmemY β).mp hβY).2 ((hX β).mp hβX).2
  rw [hunion, Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj, mul_add] at hΛeq
  have key : ∀ a b x y : ℕ, a ≤ x → b ≤ y → a + b = x + y → a = x := by
    intro a b x y h1 h2 h3
    omega
  exact key _ _ _ _ hXle hYle hΛeq

theorem lemma_3_5_ii [FaithfulSMul G Ω]
    (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω))
    [IsPreprimitive G Ω] (hO : CFSG.pPrimeCore 2 G = ⊥) {v : G} (hv : orderOf v = 2)
    {P : Subgroup (typeLSection G Ω v)} (hPn : P.Normal) (hPodd : Odd (Nat.card P)) {α : Ω}
    {Λ : Finset Ω} (hΛα : ∀ β ∈ Λ, β ≠ α)
    (hΛ : ∀ β ∈ Λ, ∀ γ, γ ≠ α → HoltSim G Ω α β γ → γ ∈ Λ) {X : Finset Ω}
    (hX : ∀ β, β ∈ X ↔ β ∈ Λ ∧ β ∈ holtNabla G Ω v P α) (hXne : X.Nonempty) :
    ∃ β ∈ X, 1 < Nat.card (holtDelta G Ω α β) := by
  have hsum := lemma_3_5_ii_sum hG hB hv hPn hPodd hΛα hΛ hX
  obtain ⟨β, hβX, hβ⟩ := Finset.exists_le_of_sum_le hXne
    (f := fun _ => Nat.card (longInvAt G Ω α)) (g := fun β => Nat.card (longInvSwap G Ω α β))
    (by rw [Finset.sum_const, smul_eq_mul, hsum, mul_comm])
  exact ⟨β, hβX, one_lt_card_holtDelta_of_le hG hO
    (Ne.symm (ne_of_mem_holtNabla ((hX β).mp hβX).2)) hβ⟩

theorem lemma_3_5_ii_exists [FaithfulSMul G Ω]
    (hG : IsStarGroup G Ω) (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω))
    [IsPreprimitive G Ω] (hO : CFSG.pPrimeCore 2 G = ⊥) {α : Ω} {v : G} (hv : orderOf v = 2)
    (hvα : v • α = α) {P : Subgroup (typeLSection G Ω v)} (hPn : P.Normal)
    (hPodd : Odd (Nat.card P)) (hP1 : P ≠ ⊥) :
    ∃ β : Ω, β ≠ α ∧ (∃ p ∈ P, ∃ a : fixSet Ω (Subgroup.zpowers v), (a : Ω) = α ∧
      ((p • a : _) : Ω) = β) ∧ 1 < Nat.card (holtDelta G Ω α β) := by
  classical
  have := Fintype.ofFinite Ω
  have hv2 := isPGroup_zpowers_of_orderOf_eq_two hv
  have hαF : α ∈ fixSet Ω (Subgroup.zpowers v) := by
    rw [fixSet_zpowers]
    exact hvα
  obtain ⟨p, hp, hpa⟩ : ∃ p ∈ P, p • (⟨α, hαF⟩ : fixSet Ω (Subgroup.zpowers v)) ≠ ⟨α, hαF⟩ := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hP1
    refine (Subgroup.eq_bot_iff_forall P).mpr fun p hp => Subtype.ext (Equiv.ext fun x => ?_)
    have := hG.isPretransitive_centralizer hv2
    obtain ⟨⟨c, hc⟩, hcx⟩ := exists_smul_eq (Subgroup.centralizer
      ((Subgroup.zpowers v : Subgroup G) : Set G)) (⟨α, hαF⟩ : fixSet Ω (Subgroup.zpowers v)) x
    set c' : typeLSection G Ω v :=
      ⟨MulAction.toPermHom _ _ (⟨c, hc⟩ : Subgroup.centralizer _), ⟨c, hc⟩, rfl⟩ with hc'
    have hc'x : c' • (⟨α, hαF⟩ : fixSet Ω (Subgroup.zpowers v)) = x := hcx
    have h1 := hcon _ (hPn.conj_mem p hp c'⁻¹)
    rw [inv_inv] at h1
    have h2 : p • x = x := by
      calc p • x = (c' * (c'⁻¹ * p * c')) • (⟨α, hαF⟩ : fixSet Ω (Subgroup.zpowers v)) := by
            rw [← hc'x, smul_smul]
            congr 1
            group
        _ = x := by rw [mul_smul, h1, hc'x]
    exact h2
  set β₀ : Ω := ((p • (⟨α, hαF⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) with hβ₀
  have hβ₀O : β₀ ∈ typeLOrbit G Ω v P α := ⟨p, hp, ⟨α, hαF⟩, rfl, rfl⟩
  have hβ₀α : β₀ ≠ α := fun h => hpa (Subtype.ext h)
  have hβ₀N : β₀ ∈ holtNabla G Ω v P α := ⟨1, one_mem _, β₀, hβ₀O, hβ₀α, one_smul G _⟩
  set X : Finset Ω := Finset.univ.filter (· ∈ holtNabla G Ω v P α) with hXdef
  have hX : ∀ β, β ∈ X ↔ β ∈ Finset.univ.erase α ∧ β ∈ holtNabla G Ω v P α := fun β => by
    simp only [hXdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact ⟨fun h => ⟨ne_of_mem_holtNabla h, h⟩, fun h => h.2⟩
  obtain ⟨β, hβX, hβΔ⟩ := lemma_3_5_ii hG hB hO hv hPn hPodd
    (Λ := Finset.univ.erase α) (fun β hβ => Finset.ne_of_mem_erase hβ)
    (fun β _ γ hγ _ => Finset.mem_erase.mpr ⟨hγ, Finset.mem_univ γ⟩) hX
    ⟨β₀, (hX β₀).mpr ⟨Finset.mem_erase.mpr ⟨hβ₀α, Finset.mem_univ _⟩, hβ₀N⟩⟩
  obtain ⟨g, hg, β₁, hβ₁, hβ₁α, rfl⟩ := ((hX β).mp hβX).2
  have hgα : g • α = α := hg
  have hcard : Nat.card (holtDelta G Ω α (g • β₁)) = Nat.card (holtDelta G Ω α β₁) := by
    rw [← hgα, ← smul_holtDelta, hgα, ← Set.image_smul,
      Nat.card_image_of_injective (MulAction.injective g)]
  obtain ⟨p', hp', a, ha, hβ₁eq⟩ := hβ₁
  exact ⟨β₁, hβ₁α, ⟨p', hp', a, ha, hβ₁eq⟩, hcard ▸ hβΔ⟩

end Lemma35ii

end CFSG.Holt.H78
