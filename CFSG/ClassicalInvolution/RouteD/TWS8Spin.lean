module

public import CFSG.ClassicalInvolution.RouteD.TWS8Geo3
public import CFSG.ClassicalInvolution.RouteD.TWS8CA
public import CFSG.ClassicalInvolution.RouteD.TWS6SCount
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Block
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalGroups.Orthogonal.Small (stabSub)
open CFSG.ClassicalInvolution.Generic (conjSub mem_conjSub_iff conj_mem_conjSub conjSub_map
  conjSub_inv_conjSub)
open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.Orth15
open CFSG.ClassicalInvolution.RouteD.TwinY
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Stab

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [FiniteDimensional F V]

omit [FiniteDimensional F V] in
theorem f₂_mem_wPlane' (fr : OFrame Q) : fr.f₂ ∈ wPlane fr :=
  ⟨!![0, 0; 1, 0], by simp [Frame.incl_apply]⟩

omit [FiniteDimensional F V] in
theorem pW_of_mem_perp {fr : OFrame Q} {a : V} (ha : a ∈ fr.perp) : pW fr a = 0 := by
  rw [pW_apply, (Frame.mem_perp_iff fr).mp ha, map_zero]

omit [FiniteDimensional F V] in
theorem pA_of_mem_perp {fr : OFrame Q} {a : V} (ha : a ∈ fr.perp) : pA fr a = a := by
  rw [pA_apply, (Frame.mem_perp_iff fr).mp ha, map_zero, sub_zero]

omit [FiniteDimensional F V] in
theorem perp_of_stabE (fr : OFrame Q) {g : V ≃ₗ[F] V} (hg : g ∈ stabE fr) {a : V}
    (ha : a ∈ fr.perp) : g a ∈ fr.perp := by
  have hO := elementaryGroup_le_orthogonalGroup Q hg.1
  rw [Frame.mem_perp_iff_forall_incl]
  intro Y
  have hW : g⁻¹ (fr.incl Y) ∈ wPlane fr := by
    have := (mem_stabE.mp hg).2 (g⁻¹ (fr.incl Y))
    rw [LinearEquiv.apply_inv_apply'] at this
    exact this.mpr (incl_mem_wPlane fr Y)
  have h1 : polar Q (g a) (fr.incl Y) = polar Q a (g⁻¹ (fr.incl Y)) := by
    rw [← polar_map_of_mem hO a (g⁻¹ (fr.incl Y)), LinearEquiv.apply_inv_apply']
  rw [h1]
  exact polar_perp_wPlane ha hW

omit [FiniteDimensional F V] in
theorem stabE_pW (fr : OFrame Q) {g : V ≃ₗ[F] V} (hg : g ∈ stabE fr) (x : V) :
    pW fr (g x) = g (pW fr x) := by
  have h1 : g (pW fr x) ∈ wPlane fr := ((mem_stabE.mp hg).2 _).mp (pW_mem fr x)
  have h2 : g (pA fr x) ∈ fr.perp := perp_of_stabE fr hg (pA_mem_perp fr x)
  have h3 : g x = g (pW fr x) + g (pA fr x) := by rw [← map_add, pW_add_pA]
  rw [h3, map_add, pW_of_mem h1, pW_of_mem_perp h2, add_zero]

omit [FiniteDimensional F V] in
theorem stabE_comm_ι (fr : OFrame Q) {g : V ≃ₗ[F] V} (hg : g ∈ stabE fr) :
    g * fr.La (-1) = fr.La (-1) * g := by
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Frame.La_neg_one_apply,
    Frame.La_neg_one_apply, map_sub, map_smul, ← pW_apply, ← pW_apply, stabE_pW fr hg]

omit [FiniteDimensional F V] in
theorem map_La_range (fr : OFrame Q) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (fr.map hg).La.range = conjSub g fr.La.range := by
  ext y
  constructor
  · rintro ⟨A, rfl⟩
    rw [Frame.map_La]
    exact conj_mem_conjSub ⟨A, rfl⟩
  · intro hy
    rw [mem_conjSub_iff] at hy
    obtain ⟨A, hA⟩ := hy
    refine ⟨A, ?_⟩
    rw [Frame.map_La, hA]
    group

omit [FiniteDimensional F V] in
theorem La_conj_range (h2 : (2 : F) ≠ 0) (fr : OFrame Q) {g : V ≃ₗ[F] V} (hg : g ∈ stabE fr) :
    (conjSub g fr.La.range = fr.La.range ∨ conjSub g fr.La.range = fr.swap.La.range) ∧
      (conjSub g fr.swap.La.range = fr.La.range ∨
        conjSub g fr.swap.La.range = fr.swap.La.range) := by
  have hO := elementaryGroup_le_orthogonalGroup Q hg.1
  have hι := stabE_comm_ι fr hg
  constructor
  · have h1 : (fr.map hO).La (-1) = fr.La (-1) := by
      rw [Frame.map_La, hι]
      group
    rw [← map_La_range fr hO]
    exact Frame.La_range_eq_or_eq_swap h2 h1
  · have h1 : (fr.swap.map hO).La (-1) = fr.La (-1) := by
      rw [Frame.map_La, Frame.La_swap_neg_one, hι]
      group
    rw [← map_La_range fr.swap hO]
    exact Frame.La_range_eq_or_eq_swap h2 h1

end Stab

section Lift

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] {Q : QuadraticForm F (ι → F)}

omit [Finite F] [Fintype ι] in
theorem conj_pair_mem (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q))
    (h2 : (2 : F) ≠ 0) {R R' : Subgroup (spinGroup Q)} (hRp : ⁅R, R⁆ = R) (hR'p : ⁅R', R'⁆ = R')
    {fr : OFrame Q} (hR : R.map (spinAction Q) = fr.La.range)
    (hR' : R'.map (spinAction Q) = fr.swap.La.range) {g : spinGroup Q}
    (hg : spinAction Q g ∈ stabE fr) :
    ∀ J ∈ ({R, R'} : Set (Subgroup (spinGroup Q))),
      conjSub g J ∈ ({R, R'} : Set (Subgroup (spinGroup Q))) := by
  have hperf : ∀ J : Subgroup (spinGroup Q), ⁅J, J⁆ = J →
      ⁅conjSub g J, conjSub g J⁆ = conjSub g J := fun J hJ => by
      unfold conjSub
      rw [← Subgroup.map_commutator, hJ]
  obtain ⟨h1, h1'⟩ := La_conj_range h2 fr hg
  have hmap : ∀ J : Subgroup (spinGroup Q), (conjSub g J).map (spinAction Q) =
      conjSub (spinAction Q g) (J.map (spinAction Q)) := fun J => (conjSub_map _ _ _).symm
  intro J hJ
  rcases hJ with rfl | hJ'
  · rcases h1 with h | h
    · left
      exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect (spinAction Q) hker
        (hperf _ hRp) hRp (by rw [hmap, hR, h])
    · right
      exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect (spinAction Q) hker
        (hperf _ hRp) hR'p (by rw [hmap, hR, h, hR'])
  · rw [Set.mem_singleton_iff] at hJ'
    subst hJ'
    rcases h1' with h | h
    · left
      exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect (spinAction Q) hker
        (hperf _ hR'p) hRp (by rw [hmap, hR', h, hR])
    · right
      exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect (spinAction Q) hker
        (hperf _ hR'p) hR'p (by rw [hmap, hR', h])

omit [Finite F] [Fintype ι] in
theorem mem_conjStabilizer_of_stabE (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q))
    (h2 : (2 : F) ≠ 0) {R R' : Subgroup (spinGroup Q)} (hRp : ⁅R, R⁆ = R) (hR'p : ⁅R', R'⁆ = R')
    {fr : OFrame Q} (hR : R.map (spinAction Q) = fr.La.range)
    (hR' : R'.map (spinAction Q) = fr.swap.La.range) {g : spinGroup Q}
    (hg : spinAction Q g ∈ stabE fr) :
    g ∈ CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
      ({R, R'} : Set (Subgroup (spinGroup Q))) := by
  rw [CFSG.ClassicalInvolution.G2D4Models.mem_conjStabilizer_iff]
  intro J
  constructor
  · intro hJ
    have hg' : spinAction Q g⁻¹ ∈ stabE fr := by
      rw [map_inv]
      exact (stabE fr).inv_mem hg
    have := conj_pair_mem hker h2 hRp hR'p hR hR' hg' (conjSub g J) hJ
    rwa [conjSub_inv_conjSub] at this
  · exact conj_pair_mem hker h2 hRp hR'p hR hR' hg J

theorem stabE_of_mem_conjStabilizer (hodd : Odd (Nat.card F))
    (hrange : (spinAction Q).range = elementaryGroup Q) {R R' : Subgroup (spinGroup Q)}
    {fr : OFrame Q} (hR : R.map (spinAction Q) = fr.La.range)
    (hR' : R'.map (spinAction Q) = fr.swap.La.range) {g : spinGroup Q}
    (hg : g ∈ CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
      ({R, R'} : Set (Subgroup (spinGroup Q)))) : spinAction Q g ∈ stabE fr := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hgR : conjSub g R ∈ ({R, R'} : Set (Subgroup (spinGroup Q))) :=
    ((CFSG.ClassicalInvolution.G2D4Models.mem_conjStabilizer_iff.mp hg) R).mpr
      (Set.mem_insert _ _)
  have hmap : (conjSub g R).map (spinAction Q) = conjSub (spinAction Q g) fr.La.range := by
    rw [← hR]
    exact (conjSub_map _ _ _).symm
  have hι : spinAction Q g * fr.La (-1) * (spinAction Q g)⁻¹ = fr.La (-1) := by
    have hmem : spinAction Q g * fr.La (-1) * (spinAction Q g)⁻¹ ∈
        conjSub (spinAction Q g) fr.La.range := conj_mem_conjSub ⟨-1, rfl⟩
    have hord : orderOf (spinAction Q g * fr.La (-1) * (spinAction Q g)⁻¹) = 2 := by
      have := orderOf_injective (MulAut.conj (spinAction Q g)).toMonoidHom
        (MulAut.conj (spinAction Q g)).injective (fr.La (-1))
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rw [this]
      exact (IsFundamental.of_frame fr).orderOf_eq_two hodd
    rcases hgR with h | h
    · rw [h, hR] at hmap
      rw [← hmap] at hmem
      exact (IsFundamental.of_frame fr).eq_of_orderOf_eq_two hodd hmem hord
    · rw [Set.mem_singleton_iff] at h
      rw [h, hR'] at hmap
      rw [← hmap] at hmem
      exact (IsFundamental.of_frame_swap fr).eq_of_orderOf_eq_two hodd hmem hord
  have hcomm : spinAction Q g * fr.La (-1) = fr.La (-1) * spinAction Q g := by
    calc spinAction Q g * fr.La (-1)
        = (spinAction Q g * fr.La (-1) * (spinAction Q g)⁻¹) * spinAction Q g := by group
      _ = fr.La (-1) * spinAction Q g := by rw [hι]
  have hW : ∀ x ∈ wPlane fr, spinAction Q g x ∈ wPlane fr := by
    intro x hx
    have h1 : fr.La (-1) x = -x := by
      rw [Frame.La_neg_one_apply, ← pW_apply, pW_of_mem hx, two_smul]
      abel
    have h2' : fr.La (-1) (spinAction Q g x) = -(spinAction Q g x) := by
      have := congrArg (fun φ : (ι → F) ≃ₗ[F] (ι → F) => φ x) hcomm
      simp only [LinearEquiv.mul_apply] at this
      rw [← this, h1, map_neg]
    rw [Frame.La_neg_one_apply, ← pW_apply] at h2'
    have h3 : (2 : F) • (spinAction Q g x - pW fr (spinAction Q g x)) = 0 := by
      calc (2 : F) • (spinAction Q g x - pW fr (spinAction Q g x))
          = (spinAction Q g x - (2 : F) • pW fr (spinAction Q g x)) - (-(spinAction Q g x)) := by
            module
        _ = 0 := by rw [h2', sub_self]
    have h4 := (smul_eq_zero.mp h3).resolve_left h2
    have h5 : spinAction Q g x = pW fr (spinAction Q g x) := sub_eq_zero.mp h4
    rw [h5]
    exact pW_mem fr _
  refine ⟨?_, mem_stabSub_of_mapsTo hW⟩
  have : spinAction Q g ∈ (spinAction Q).range := ⟨g, rfl⟩
  rwa [hrange] at this

end Lift

section Coatom

variable {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {F : Type} [Field F] [Finite F] {ι : Type}
  [Fintype ι] {Q : QuadraticForm F (ι → F)}
  {D : CFSG.LieType.Universal.UniversalRootDatum (spinGroup Q)}

theorem eq_top_of_sup_center_eq_top_of_isPerfect' {X : Type*} [Group X] [Group.IsPerfect X]
    {S : Subgroup X} (h : S ⊔ Subgroup.center X = ⊤) : S = ⊤ := by
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := X), commutator_def,
    Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨b, hb, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  have hc' := Subgroup.mem_center_iff.mp hc
  have hd' := Subgroup.mem_center_iff.mp hd
  have : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
        = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * (b * c) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hc' b]
      _ = a * b * (c * (d * c⁻¹)) * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * b * (c * (c⁻¹ * d)) * a⁻¹ * d⁻¹ * b⁻¹ := by
          rw [(Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) d).symm]
      _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [hd' a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [this, commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)

theorem isCoatom_conjStabilizer (c : TWS6.SpinCtxS t Q D)
    (hA : ∀ fr : OFrame Q, Module.finrank F fr.perp < 4 ∨ NoTotSing Q fr.perp)
    {R R' : Subgroup (spinGroup Q)} {x x' : spinGroup Q}
    (hd : TwinDatumOn t ⟨spinGroup Q, D⟩ R R' x x') :
    IsCoatom (CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
      ({R, R'} : Set (Subgroup (spinGroup Q)))) := by
  classical
  have := c.perfect
  have hker := ker_spinAction_le_center Q
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card c.hodd
  have hperfS : ∀ S : Subgroup (spinGroup Q), S ≤ ⁅S, S⁆ → ⁅S, S⁆ = S := fun S hS =>
    le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb =>
      S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)) hS
  have hRp : ⁅R, R⁆ = R := hperfS R (c.hperf R hd.mem)
  have hR'p : ⁅R', R'⁆ = R' := hperfS R' (c.hperf R' hd.mem')
  obtain ⟨fr, hR, hR', -, -⟩ := exists_pair_frame c.hodd c.hrange c.hZ (by have := c.hV; omega)
    c.hproj (c.hperf R hd.mem) (c.hperf R' hd.mem') (c.hcorr R hd.mem) (c.hcorr R' hd.mem')
    (c.hnc R hd.mem) (c.hnc R' hd.mem') hd.ne hd.hx hd.cx hd.nx hd.hx' hd.cx' hd.nx' hd.same
  have hN : ∀ g : spinGroup Q, g ∈ CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
      ({R, R'} : Set (Subgroup (spinGroup Q))) ↔ spinAction Q g ∈ stabE fr := fun g =>
    ⟨stabE_of_mem_conjStabilizer c.hodd c.hrange hR hR',
      mem_conjStabilizer_of_stabE hker h2 hRp hR'p hR hR'⟩
  have h3 : 3 ≤ Module.finrank F fr.perp := by
    have := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    have := c.hV
    omega
  refine ⟨?_, fun M hM => ?_⟩
  · intro htop
    obtain ⟨a, ha, ha0⟩ : ∃ a ∈ fr.perp, a ≠ 0 := by
      refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
      rw [h, finrank_bot] at h3
      omega
    have hEa : eichler Q fr.e₁ a ∈ (spinAction Q).range := by
      rw [c.hrange]
      exact eichler_mem_elementaryGroup Q _ _
    obtain ⟨g, hg⟩ := hEa
    have hgN : g ∈ CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
        ({R, R'} : Set (Subgroup (spinGroup Q))) := by
      rw [htop]
      trivial
    have hgW := (hN g).mp hgN
    rw [hg] at hgW
    have hpolar : polar Q fr.e₁ a = 0 := polar_wPlane_perp ha (e₁_mem_wPlane fr)
    have hmem := ((mem_stabE.mp hgW).2 fr.f₁).mp (f₁_mem_wPlane fr)
    rw [eichler_apply fr.Q_e₁ hpolar] at hmem
    have h0 := pA_of_mem hmem
    rw [map_sub, map_add, map_smul, map_smul, pA_of_mem (f₁_mem_wPlane fr),
      pA_of_mem (e₁_mem_wPlane fr), pA_of_mem_perp ha, fr.polar_f₁_e₁] at h0
    simp at h0
    exact ha0 h0
  · obtain ⟨h, hhM, hhN⟩ := IsConcreteLE.exists_of_lt hM
    have hhE : spinAction Q h ∈ elementaryGroup Q := by
      rw [← c.hrange]
      exact ⟨h, rfl⟩
    have hhθ : ¬ ∀ y ∈ wPlane fr, spinAction Q h y ∈ wPlane fr := fun hall =>
      hhN ((hN h).mpr ⟨hhE, mem_stabSub_of_mapsTo hall⟩)
    have hHE : M.map (spinAction Q) ≤ elementaryGroup Q := by
      rw [← c.hrange]
      exact Subgroup.map_le_range _ _
    have hH : stabE fr ≤ M.map (spinAction Q) := by
      intro y hy
      obtain ⟨g, hg⟩ : y ∈ (spinAction Q).range := by
        rw [c.hrange]
        exact hy.1
      exact ⟨g, hM.le ((hN g).mpr (hg ▸ hy)), hg⟩
    have hEle := elementaryGroup_le_of_not_maps c.hodd c.hQ fr hH hHE h3 (hA fr)
      (Subgroup.mem_map_of_mem _ hhM) hhθ
    have hsup : M ⊔ Subgroup.center (spinGroup Q) = ⊤ := by
      rw [eq_top_iff]
      intro k _
      have hk : spinAction Q k ∈ elementaryGroup Q := by
        rw [← c.hrange]
        exact ⟨k, rfl⟩
      obtain ⟨m, hm, hmk⟩ := hEle hk
      refine Subgroup.mem_sup_of_normal_right.mpr ⟨m, hm, m⁻¹ * k, hker ?_, mul_inv_cancel_left m k⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmk, inv_mul_cancel]
    exact eq_top_of_sup_center_eq_top_of_isPerfect' hsup

end Coatom

section Minus

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

omit [FiniteDimensional F V] in
theorem noTotSing_of_not_isPlusType (hP : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hdim : Module.finrank F V = 8) (fr : OFrame Q) : NoTotSing Q fr.perp := by
  intro u hu v hv hQu hQv huv
  by_contra hcon
  push Not at hcon
  obtain ⟨hu0, hvc⟩ := hcon
  have he₁ := e₁_mem_wPlane fr
  have he₂ := e₂_mem_wPlane fr
  have hf₁ := f₁_mem_wPlane fr
  have hf₂ := f₂_mem_wPlane' fr
  have hli : LinearIndependent F (![fr.e₁, fr.e₂, u, v] : Fin 4 → V) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • fr.e₁ + g 1 • fr.e₂ + g 2 • u + g 3 • v = 0 := by
      simpa [Fin.sum_univ_four] using hg
    clear hg
    have hg := hg'
    have h1 := congrArg (fun y => polar Q y fr.f₁) hg
    have h2 := congrArg (fun y => polar Q y fr.f₂) hg
    have p1 : polar Q u fr.f₁ = 0 := polar_perp_wPlane hu hf₁
    have p2 : polar Q v fr.f₁ = 0 := polar_perp_wPlane hv hf₁
    have p3 : polar Q u fr.f₂ = 0 := polar_perp_wPlane hu hf₂
    have p4 : polar Q v fr.f₂ = 0 := polar_perp_wPlane hv hf₂
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, polar_zero_left, fr.polar_e₁_f₁,
      fr.polar_e₂_f₁, fr.polar_e₁_f₂, fr.polar_e₂_f₂, p1, p2, p3, p4] at h1 h2
    have g0 : g 0 = 0 := by simpa using h1
    have g1 : g 1 = 0 := by simpa using h2
    rw [g0, g1, zero_smul, zero_smul, zero_add, zero_add] at hg
    have g3 : g 3 = 0 := by
      by_contra h3
      apply hvc (-(g 2) / g 3)
      have : g 3 • v = -(g 2) • u := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_right hg
      calc v = (g 3)⁻¹ • (g 3 • v) := by rw [smul_smul, inv_mul_cancel₀ h3, one_smul]
        _ = (-(g 2) / g 3) • u := by rw [this, smul_smul, div_eq_inv_mul, mul_comm]
    rw [g3, zero_smul, add_zero] at hg
    have g2 : g 2 = 0 := (smul_eq_zero.mp hg).resolve_right hu0
    intro i
    fin_cases i <;> simp [g0, g1, g2, g3]
  have pee : polar Q fr.e₁ fr.e₁ = 0 := polar_self_eq_zero fr.Q_e₁
  have pee' : polar Q fr.e₂ fr.e₂ = 0 := polar_self_eq_zero fr.Q_e₂
  have puu : polar Q u u = 0 := polar_self_eq_zero hQu
  have pvv : polar Q v v = 0 := polar_self_eq_zero hQv
  have pvu : polar Q v u = 0 := by rw [polar_comm]; exact huv
  have a1 : polar Q fr.e₁ u = 0 := polar_wPlane_perp hu he₁
  have a2 : polar Q fr.e₁ v = 0 := polar_wPlane_perp hv he₁
  have a3 : polar Q fr.e₂ u = 0 := polar_wPlane_perp hu he₂
  have a4 : polar Q fr.e₂ v = 0 := polar_wPlane_perp hv he₂
  have b1 : polar Q u fr.e₁ = 0 := polar_perp_wPlane hu he₁
  have b2 : polar Q v fr.e₁ = 0 := polar_perp_wPlane hv he₁
  have b3 : polar Q u fr.e₂ = 0 := polar_perp_wPlane hu he₂
  have b4 : polar Q v fr.e₂ = 0 := polar_perp_wPlane hv he₂
  have hTs : ∀ x ∈ Submodule.span F (Set.range (![fr.e₁, fr.e₂, u, v] : Fin 4 → V)),
      Q x = 0 := by
    intro x hx
    refine map_eq_zero_of_mem_span (S := Set.range (![fr.e₁, fr.e₂, u, v] : Fin 4 → V)) ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [fr.Q_e₁, fr.Q_e₂, hQu, hQv]
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      fin_cases i <;> fin_cases j <;>
        simp [pee, pee', puu, pvv, pvu, huv, a1, a2, a3, a4, b1, b2, b3, b4, fr.polar_e₁_e₂,
          fr.polar_e₂_e₁]
  have hT4 : Module.finrank F (Submodule.span F (Set.range (![fr.e₁, fr.e₂, u, v] : Fin 4 → V)))
      = 4 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  exact hP ⟨_, by rw [hT4, hdim], hTs⟩

end Minus

section Rows

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD.TWY
open CFSG.GroupTheory.WeirSylow (IsPlusType not_isPlusType_quadMinus)

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


theorem twinPairMax_odd3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : TwinPairMax p f .POmegaOdd 3 := by
  intro R R' x x' hd
  have he : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 3 p f := ⟨Fact.out, he, by omega, hp2⟩
  have key : ∀ M : LieUniversal,
      M = ⟨spinGroup (quadOdd 3 (GaloisField p f)), oddDatum 3 (GaloisField p f)⟩ →
      ∀ {R R' : Subgroup M.K} {x x' : M.K}, TwinDatumOn .POmegaOdd M R R' x x' →
        IsCoatom (CFSG.ClassicalInvolution.G2D4Models.conjStabilizer
          ({R, R'} : Set (Subgroup M.K))) := by
    intro M hM
    subst hM
    intro R R' x x' hd
    refine isCoatom_conjStabilizer (TWS6.spinCtxS_odd hp2 hq (le_refl 3) hadm)
      (fun fr => Or.inl ?_) hd
    have h1 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    have hdim : Module.finrank (GaloisField p f) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) = 7 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_unit]
    omega
  exact key _ rfl hd.toOn

theorem twinPairMax_minus4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : TwinPairMax p f .POmegaMinus 4 := by
  intro R R' x x' hd
  have he : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus 4 p f := ⟨Fact.out, he, le_refl 4⟩
  have c := TWS6.spinCtxS_minus hp2 hq (le_refl 4) hadm
  have hdim : Module.finrank (GaloisField p f)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have hP : ¬ IsPlusType (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) := not_isPlusType_quadMinus (by omega) (minusCoeffs_irr p f)
  exact isCoatom_conjStabilizer c (fun fr => Or.inr (noTotSing_of_not_isPlusType hP hdim fr))
    hd.toOn

end Rows

section Final

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


theorem twinYNoCentralOn_odd3 : TwinYNoCentralOn p f fun t n => t = .POmegaOdd ∧ n = 3 := by
  by_cases h : p ≠ 2 ∧ 5 ≤ p ^ f
  · exact twinYNoCentralOn_odd3_of_twinPairMax (twinPairMax_odd3 h.1 h.2)
  · intro G _ _ _ hnab K z S
    exact absurd ⟨S.odd, S.five⟩ h

theorem twinYNoCentralOn_minus4 : TwinYNoCentralOn p f fun t n => t = .POmegaMinus ∧ n = 4 := by
  by_cases h : p ≠ 2 ∧ 5 ≤ p ^ f
  · exact twinYNoCentralOn_minus4_of_twinPairMax (twinPairMax_minus4 h.1 h.2)
  · intro G _ _ _ hnab K z S
    exact absurd ⟨S.odd, S.five⟩ h

end Final

end CFSG.ClassicalInvolution.RouteD.TWS8
