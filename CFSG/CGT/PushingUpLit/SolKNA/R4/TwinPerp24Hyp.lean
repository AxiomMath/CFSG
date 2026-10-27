module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Vertex
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23Sub
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Cube

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {W K K' : Subgroup Y} {t : Y}

@[expose] def cube (D : Perp23.Two.TwoFrame Ω W K K' t) : Subgroup Y :=
  Subgroup.closure ({t, D.F.j, vertex D} : Set Y)

variable (D : Perp23.Two.TwoFrame Ω W K K' t)
  (hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hm : Even D.m) (hju : D.F.j = D.b * D.b'⁻¹)

include hc hm hju

private theorem comm_gen : ∀ a ∈ ({t, D.F.j, vertex D} : Set Y), ∀ b ∈ ({t, D.F.j, vertex D} : Set Y),
    a * b = b * a := by
  have hW : ∀ a ∈ ({t, D.F.j, vertex D} : Set Y), a ∈ W := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact D.t_mem_W
    · exact D.j_mem_W
    · exact vertex_mem_W D hc hm
  intro a ha b hb
  exact hc a (hW a ha) b (hW b hb)

private theorem sq_gen : ∀ a ∈ ({t, D.F.j, vertex D} : Set Y), a * a = 1 := by
  intro a ha
  rcases ha with rfl | rfl | rfl
  · exact (Perp23.Two.TwoFrame.hzK D).sq
  · exact D.j_sq
  · exact vertex_sq_eq D hc hm hju

theorem isElemAbelian_cube : IsElemAbelian 2 (cube D) := by
  have hcomm := ChainFrame.commutes_closure (comm_gen D hc hm hju)
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact ChainFrame.sq_closure (sq_gen D hc hm hju) (comm_gen D hc hm hju) x hx

theorem card_cube : Nat.card (cube D) = 8 := by
  obtain ⟨hv1, hvt, hvj, hvtj⟩ := vertex_ne D hc hm hju
  have hz1 : t ≠ 1 := (Perp23.Two.TwoFrame.hzK D).ne_one
  have hj1 : D.F.j ≠ 1 := D.F.hj.ne_one
  have hjt : D.F.j ≠ t := by
    intro h
    have e := D.s_t hc
    rw [h, (Perp23.Two.TwoFrame.hzK D).sq] at e
    apply hz1
    have : t = D.F.ρ₃.r⁻¹ * (D.F.ρ₃.r * t * D.F.ρ₃.r⁻¹) * D.F.ρ₃.r := by group
    rw [this, e]
    group
  exact ChainFrame.card_closure_triple_eq_eight (sq_gen D hc hm hju t (by simp))
    (sq_gen D hc hm hju _ (by simp)) (sq_gen D hc hm hju _ (by simp))
    (comm_gen D hc hm hju t (by simp) _ (by simp)) (comm_gen D hc hm hju t (by simp) _ (by simp))
    (comm_gen D hc hm hju _ (by simp) _ (by simp)) hz1 hj1 hjt hv1 hvt hvj hvtj

omit hc hm hju in
theorem mem_normalizer_closure_triple {a b c g : Y}
    (ha : g * a * g⁻¹ ∈ Subgroup.closure ({a, b, c} : Set Y))
    (hb : g * b * g⁻¹ ∈ Subgroup.closure ({a, b, c} : Set Y))
    (hc : g * c * g⁻¹ ∈ Subgroup.closure ({a, b, c} : Set Y)) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({a, b, c} : Set Y) : Set Y) := by
  set B := Subgroup.closure ({a, b, c} : Set Y) with hB
  have hle : B ≤ B.comap (MulAut.conj g).toMonoidHom := by
    rw [hB, Subgroup.closure_le]
    rintro x (rfl | rfl | hx)
    · exact ha
    · exact hb
    · rw [Set.mem_singleton_iff.mp hx]; exact hc
  have hle' : conjSub g B ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hle hx
  have hcard : Nat.card B ≤ Nat.card (conjSub g B) := by
    unfold conjSub
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge hle' hcard)

theorem hyp51_cube (ht : Hyp51At (cube D) t) (hv : Hyp51At (cube D) (vertex D)) :
    Hyp51 (cube D) := by
  obtain ⟨hv1, hvt, hvj, hvtj⟩ := vertex_ne D hc hm hju
  have hz2 : t * t = 1 := (Perp23.Two.TwoFrame.hzK D).sq
  have hrt : D.F.ρ.r * t * D.F.ρ.r⁻¹ = t := by rw [D.r_t]; group
  have hr't : D.F.ρ'.r * t * D.F.ρ'.r⁻¹ = t := by
    have := (Perp23.Two.TwoFrame.hzK' D).commute_of_mem D.r'_mem_K'
    rw [← this]; group
  have hrj := D.r_j hc
  have hr'j := D.t_j hc
  have hsj := D.s_j
  have hst := D.s_t hc
  have hrv := vertex_r_eq D hc hm
  have hr'v := vertex_r'_eq D hc hm
  have hsv := vertex_s_eq D hc hm
  have hcomm := comm_gen D hc hm hju
  have htj : t * D.F.j = D.F.j * t := hcomm t (by simp) _ (by simp)
  have htv : t * vertex D = vertex D * t := hcomm t (by simp) _ (by simp)
  have hjv : D.F.j * vertex D = vertex D * D.F.j := hcomm _ (by simp) _ (by simp)
  have ht' : t ∈ cube D := Subgroup.subset_closure (by simp)
  have hj' : D.F.j ∈ cube D := Subgroup.subset_closure (by simp)
  have hv' : vertex D ∈ cube D := Subgroup.subset_closure (by simp)
  have hjt' : D.F.j * t ∈ cube D := (cube D).mul_mem hj' ht'
  have hvt' : vertex D * t ∈ cube D := (cube D).mul_mem hv' ht'
  have htj' : t * D.F.j ∈ cube D := (cube D).mul_mem ht' hj'
  have hvj' : vertex D * D.F.j ∈ cube D := (cube D).mul_mem hv' hj'
  have hrN : D.F.ρ.r ∈ Subgroup.normalizer (cube D : Set Y) :=
    mem_normalizer_closure_triple (by rw [hrt]; exact ht') (by rw [hrj]; exact hjt')
      (by rw [hrv]; exact hvt')
  have hr'N : D.F.ρ'.r ∈ Subgroup.normalizer (cube D : Set Y) :=
    mem_normalizer_closure_triple (by rw [hr't]; exact ht') (by rw [hr'j]; exact hjt')
      (by rw [hr'v]; exact hv')
  have hsN : D.F.ρ₃.r ∈ Subgroup.normalizer (cube D : Set Y) :=
    mem_normalizer_closure_triple (by rw [hst]; exact htj') (by rw [hsj]; exact hj')
      (by rw [hsv]; exact hvj')
  have hrs : (D.F.ρ.r * D.F.ρ₃.r) * t * (D.F.ρ.r * D.F.ρ₃.r)⁻¹ = D.F.j := by
    calc (D.F.ρ.r * D.F.ρ₃.r) * t * (D.F.ρ.r * D.F.ρ₃.r)⁻¹
        = D.F.ρ.r * (D.F.ρ₃.r * t * D.F.ρ₃.r⁻¹) * D.F.ρ.r⁻¹ := by group
      _ = D.F.ρ.r * (t * D.F.j) * D.F.ρ.r⁻¹ := by rw [hst]
      _ = (D.F.ρ.r * t * D.F.ρ.r⁻¹) * (D.F.ρ.r * D.F.j * D.F.ρ.r⁻¹) := by group
      _ = t * (D.F.j * t) := by rw [hrt, hrj]
      _ = (t * D.F.j) * t := by group
      _ = (D.F.j * t) * t := by rw [htj]
      _ = D.F.j := by rw [mul_assoc, hz2, mul_one]
  have hr's : (D.F.ρ'.r * D.F.ρ₃.r) * vertex D * (D.F.ρ'.r * D.F.ρ₃.r)⁻¹ =
      vertex D * (D.F.j * t) := by
    calc (D.F.ρ'.r * D.F.ρ₃.r) * vertex D * (D.F.ρ'.r * D.F.ρ₃.r)⁻¹
        = D.F.ρ'.r * (D.F.ρ₃.r * vertex D * D.F.ρ₃.r⁻¹) * D.F.ρ'.r⁻¹ := by group
      _ = D.F.ρ'.r * (vertex D * D.F.j) * D.F.ρ'.r⁻¹ := by rw [hsv]
      _ = (D.F.ρ'.r * vertex D * D.F.ρ'.r⁻¹) * (D.F.ρ'.r * D.F.j * D.F.ρ'.r⁻¹) := by group
      _ = vertex D * (D.F.j * t) := by rw [hr'v, hr'j]
  have hcomm8 : t * (D.F.j * vertex D) = vertex D * (D.F.j * t) := by
    calc t * (D.F.j * vertex D) = t * (vertex D * D.F.j) := by rw [hjv]
      _ = (t * vertex D) * D.F.j := by group
      _ = (vertex D * t) * D.F.j := by rw [htv]
      _ = vertex D * (t * D.F.j) := by group
      _ = vertex D * (D.F.j * t) := by rw [htj]
  refine ExactLayer.hyp51_of_orbitReps (R := {t, vertex D}) (isElemAbelian_cube D hc hm hju)
    (card_cube D hc hm hju) ?_ ?_
  · rintro r (rfl | hr)
    · exact ht
    · rw [Set.mem_singleton_iff.mp hr]; exact hv
  · intro x hx hx1
    rcases ChainFrame.mem_closure_eight hz2 D.j_sq (vertex_sq_eq D hc hm hju) htj htv hjv hx with
      h | h | h | h | h | h | h | h
    · exact absurd h hx1
    · exact ⟨t, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨t, by simp, D.F.ρ.r * D.F.ρ₃.r, Subgroup.mul_mem _ hrN hsN, by rw [h, hrs]⟩
    · exact ⟨vertex D, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨t, by simp, D.F.ρ₃.r, hsN, by rw [h, ← hst]⟩
    · exact ⟨vertex D, by simp, D.F.ρ.r, hrN, by rw [h, hrv, htv]⟩
    · exact ⟨vertex D, by simp, D.F.ρ₃.r, hsN, by rw [h, hsv, hjv]⟩
    · exact ⟨vertex D, by simp, D.F.ρ'.r * D.F.ρ₃.r, Subgroup.mul_mem _ hr'N hsN,
        by rw [h, hr's, hcomm8]⟩

end Cube

section Vacuous

variable {G : Type} [Group G] [Finite G]

open CFSG.ClassicalInvolution.Balance in
theorem commute_of_tightInO2 {X : Type} [Group X] [Finite X] {x : X}
    (hx : CFSG.ClassicalInvolution.Q3.TightInO2 x) {L : Subgroup X} (hL : CFSG.IsComponent L) :
    ∀ y ∈ L, x * y = y * x := by
  obtain ⟨Q, hQn, hQ2, hxQ⟩ := hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥Q := hQ2.isNilpotent
  have hsolv : Group.IsSolvable ↥Q := inferInstance
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hsolv hQn.isSubnormal).1 L hL
  intro y hy
  have h1 : ⁅y, x⁆ ∈ ⁅L, Q⁆ := Subgroup.commutator_mem_commutator hy hxQ
  rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at h1
  calc x * y = (y * x * y⁻¹ * x⁻¹) * (x * y) := by rw [h1, one_mul]
    _ = y * x := by group

open CFSG.ClassicalInvolution.Balance in
theorem hyp51At_of_commute {B : Subgroup G} {c b : G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B)
    (hc1 : c ≠ 1) (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c)
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    (h : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk c ⟨b, hbC⟩ * y = y * oddQuotMk c ⟨b, hbC⟩) : Hyp51At B c := by
  have hnot : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → ¬ MovedByAll B c L := by
    intro L hL hm
    obtain ⟨y, hyL, hy⟩ := hm _ (oddQuotMk_mem_modOdd hbB hbC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC)
    exact hy (h L hL y hyL)
  exact ⟨fun L L' hL _ hm _ => absurd hm (hnot L hL), fun L hL hm => absurd hm (hnot L hL)⟩

end Vacuous

section Twin


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem twin_facts (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R) :
    (∀ x ∈ tightCore R, ∃ k : ℕ, x ^ 2 ^ k ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y))) ∧
    (∀ x ∈ K', ∃ k : ℕ, x ^ 2 ^ k ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y))) ∧
    (∀ a ∈ tightCore R, ∀ b ∈ K',
      a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y))) ∧
    (∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ x ∈ tightCore R ⊔ K',
      c * x * c⁻¹ ∈ tightCore R ⊔ K') := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set K := tightCore R with hKdef
  have hKΩ : K ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hΩ : HypOmegaGen Ω := h.core.hyp
  have hK'Ω : K' ∈ Ω := hK'.1
  have hpair : twinSet Ω K = {K, K'} := TwinPerp.twinSet_eq_pair h2 hK' hne
  have hz : IsUniqueInvolution K t := Inner.isUniqueInvolution_core h.core.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hK'
  have hz2 : t * t = 1 := hz.sq
  have hz1 : t ≠ 1 := hz.ne_one
  have hKtw : K ∈ twinSet Ω K := mem_twinSet_self hKΩ hz
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  have hhull : K ⊔ K' = ⨆ J ∈ twinSet Ω K, J := by
    refine le_antisymm (sup_le (le_iSup₂_of_le K hKtw le_rfl) (le_iSup₂_of_le K' hK' le_rfl))
      (iSup₂_le fun J hJ => ?_)
    rw [hpair] at hJ
    rcases hJ with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hsubK : IsSubnormal K C := h.partIHypG.cls.isSubnormal_of_uniqueInvolution hKΩ hz
  have hsubK' : IsSubnormal K' C := h.partIHypG.cls.isSubnormal_of_uniqueInvolution hK'Ω hz'
  have hOK : oddCoreIn K ≤ oddCoreIn C := oddCoreIn_le_of_isSubnormal hsubK
  have hOK' : oddCoreIn K' ≤ oddCoreIn C := oddCoreIn_le_of_isSubnormal hsubK'
  have h2K := Perp23.isPGroup_quot_of_member h hKΩ
  have h2K' := Perp23.isPGroup_quot_of_member h hK'Ω
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun a ha b hb => ?_, fun c hc x hx => ?_⟩
  · obtain ⟨k, hk⟩ := Perp23.exists_pow_mem_oddCoreIn h2K hx
    exact ⟨k, hOK hk⟩
  · obtain ⟨k, hk⟩ := Perp23.exists_pow_mem_oddCoreIn h2K' hx
    exact ⟨k, hOK' hk⟩
  · have h4 := hΩ.omega4 K hKΩ K' hK'Ω hne.symm
    have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    have hdvd : 2 ∣ Nat.card ↥(K ⊓ K') := by
      have := Subgroup.orderOf_dvd_natCard (K ⊓ K') (x := t) ⟨hz.mem, hz'.mem⟩
      rwa [hord] at this
    have hpos : Nat.card ↥(K ⊓ K') ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ padicValNat 2 (Nat.card ↥(K ⊓ K')) :=
      one_le_padicValNat_of_dvd hpos hdvd
    have h5 := h4.2 (le_antisymm h4.1 h1)
    have hm : ⁅a, b⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator ha hb
    have := (h5 hm).1
    rw [commutatorElement_def] at this
    exact hOK this
  · rw [hhull] at hx ⊢
    exact h.conj_mem_twinHull hc hx

theorem hyp51At_cube_t (hr : 4 ≤ r) (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R)
    {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hnc : ¬ TwinPerp.WCentralNontrivial W) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R)
    (D : Perp23.Two.TwoFrame (CoreAssembly.conjClass (tightCore R)) W (tightCore R) K' t) :
    Hyp51At (cube D) t := by
  classical
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.core.hyp
  have hc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := WTool.comm_of_mem_wSet hΩ hW
  have hju := frame_ju h hW hnc D
  have hm : Even D.m := twoFrame_m_even hr h hW D
  have hfac := frame_frattini hr h h2 hW hnc hK' hne D
  obtain ⟨hK2, hK'2, hcomm, hnorm⟩ := twin_facts h h2 hK' hne
  have hz : IsUniqueInvolution (tightCore R) t := D.hzK
  have hz2 : t * t = 1 := hz.sq
  have hz1 : t ≠ 1 := hz.ne_one
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hK'
  have hKC : tightCore R ≤ Subgroup.centralizer ({t} : Set Y) :=
    CFSG.ClassicalInvolution.Asc77.isUniqueInvolution_le_centralizer hz
  have hK'C : K' ≤ Subgroup.centralizer ({t} : Set Y) :=
    CFSG.ClassicalInvolution.Asc77.isUniqueInvolution_le_centralizer hz'
  have hj2 : D.F.j * D.F.j = 1 := D.j_sq
  have htj : t * D.F.j = D.F.j * t := hc t D.t_mem_W D.F.j D.j_mem_W
  have hjC : D.F.j ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htj.symm
  have htC : t ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set E : Subgroup Y := Subgroup.closure ({t, D.F.j} : Set Y) with hEdef
  have hEp : IsPGroup 2 E := isPGroup_two_of_sq (closure_pair_sq hz2 hj2 htj)
  have hEC : E ≤ Subgroup.centralizer ({t} : Set Y) := by
    rw [hEdef, Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]; exact htC
    · rw [Set.mem_singleton_iff.mp hx]; exact hjC
  have hjE : D.F.j ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have htrans : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      ∃ x ∈ (tightCore R ⊔ K') ⊔ oddCoreIn (Subgroup.centralizer ({t} : Set Y)),
        conjSub x E = conjSub c E := by
    intro c hc'
    obtain ⟨o, ho, n, -, hn, rfl⟩ := hfac c hc'
    exact ⟨o, Subgroup.mem_sup_right ho, by rw [conjSub_mul, mem_normalizer_iff_conjSub_eq.mp hn]⟩
  obtain ⟨Pb, hPn, hP2, hPb⟩ :=
    Perp23.tightInO2_of_trans hKC hK'C hEC hEp hK2 hK'2 hcomm hnorm htrans
  have hT : TightInO2 (oddQuotMk t ⟨D.F.j, hjC⟩) := ⟨Pb, hPn, hP2, hPb D.F.j hjE⟩
  have hjt : D.F.j ≠ t := by
    intro h1
    have e := D.s_t hc
    rw [h1, hz2] at e
    apply hz1
    have : t = D.F.ρ₃.r⁻¹ * (D.F.ρ₃.r * t * D.F.ρ₃.r⁻¹) * D.F.ρ₃.r := by group
    rw [this, e]
    group
  exact hyp51At_of_commute (isElemAbelian_cube D hc hm hju) (c := t) (b := D.F.j)
    (Subgroup.subset_closure (by simp)) hz1 (Subgroup.subset_closure (by simp)) D.F.hj.ne_one hjt
    hjC fun L hL => commute_of_tightInO2 hT hL

end Twin

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
