module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthFacts
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal
open CFSG.Open (classicalInvolutionOddCore)
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

namespace TypeEPattern

variable {G : Type} [Group G]

omit [Fact p.Prime] in
theorem conjSub_conjSub_self {t : G} (h2t : t * t = 1) (L : Subgroup G) :
    conjSub t (conjSub t L) = L := by
  rw [← conjSub_mul, h2t, conjSub_one]

theorem conjSub_mem_centralizingMembers {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {t z : G}
    (htz : t * z * t⁻¹ = z) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) :
    conjSub t L ∈ centralizingMembers Ω {z} := by
  have := centralizingMembers_conj hΩ t z
  rw [htz] at this
  rw [this]
  exact ⟨L, hL, rfl⟩

end TypeEPattern

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

omit [Finite G] in
theorem conjSub_layer_member (c : ETCtx p f tY nY Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) :
    conjSub t N ∈ centralizingMembers Ω {z} ∧ conjSub t N ≠ K := by
  refine ⟨TypeEPattern.conjSub_mem_centralizingMembers c.hΩ.conjInvariant htz hN, fun h => hNK ?_⟩
  have := congrArg (conjSub t) h
  rwa [TypeEPattern.conjSub_conjSub_self h2t, hKt] at this

theorem locAut_mem_range (c : ETCtx p f tY nY Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K)
    (hgen : c.d.ψ.range ≤ ⨆ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      R.map c.d.ψ) (k : (modelUniv tY nY p f Fact.out).K) :
    Gaps.locAut c.hΩ.conjInvariant htz (c.d.ψ k) ∈ c.d.ψ.range := by
  have hS : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      (R.map c.d.ψ).map (Gaps.locAut c.hΩ.conjInvariant htz).toMonoidHom ≤ c.d.ψ.range := by
    intro R hR
    obtain ⟨N, hNz, hNK, hNeq⟩ := c.exists_member_of_fund hR
    obtain ⟨hN'z, hN'K⟩ := c.conjSub_layer_member htz h2t hKt hNz hNK
    obtain ⟨R', -, hR'eq⟩ := c.exists_fund_of_ne hN'z hN'K
    rw [← hNeq, Gaps.locAut_locImg c.hΩ.conjInvariant htz, hR'eq]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hmap : c.d.ψ.range.map (Gaps.locAut c.hΩ.conjInvariant htz).toMonoidHom ≤ c.d.ψ.range := by
    refine (Subgroup.map_mono hgen).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hR => hS R hR
  exact hmap ⟨_, ⟨k, rfl⟩, rfl⟩

end ETCtx

section Geometry

variable {KY : Type} [Group KY]

structure SignPerp (𝓕 : Set (Subgroup KY)) (F : Type) [Field F] [Finite F] : Prop where
  sign : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ∀ R₃ ∈ 𝓕, Gaps.ModelAdj (Subgroup.center KY) R₁ R₂ →
    Gaps.ModelAdj (Subgroup.center KY) R₃ R₂ → Commutes R₁ R₃ →
    (∃ W, LinearBlockStandardPair F W R₁ R₂) → ∃ W, LinearBlockStandardPair F W R₂ R₃
  perp2 : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, Gaps.ModelAdj (Subgroup.center KY) R₁ R₂ →
    (∃ W, LinearBlockStandardPair F W R₁ R₂) →
    ∃ S₁ ∈ 𝓕, ∃ S₂ ∈ 𝓕, S₁ ≠ S₂ ∧ Commutes R₁ S₁ ∧ Commutes R₁ S₂ ∧ ¬ Commutes R₂ S₁ ∧
      ¬ Commutes R₂ S₂

structure LayerGeom (𝓕 : Set (Subgroup KY)) (F : Type) [Field F] [Finite F] : Prop
    extends SignPerp 𝓕 F where
  lift : ∀ {X : Type} [Group X] (ψ : KY →* X), ψ.ker ≤ Subgroup.center KY →
    ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, (∃ W, LinearBlockStandardPair F W (R₁.map ψ) (R₂.map ψ)) →
      ∃ W, LinearBlockStandardPair F W R₁ R₂

theorem Gaps.OrthFacts.toLayerGeom {𝓕 : Set (Subgroup KY)} {F : Type} [Field F] [Finite F]
    (h : Gaps.OrthFacts 𝓕 F) : LayerGeom 𝓕 F :=
  ⟨⟨h.sign, h.perp2⟩, h.lift⟩

end Geometry

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem exists_ctx_member (c : ETCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 1 tY nY Ω z) {M : Subgroup G} (hM : M ∈ Ω) {x : G}
    (hx : IsClassicalMember p f M x) : Nonempty (ETCtx p f tY nY Ω M x) := by
  obtain ⟨g, hg⟩ := hsingle M hM
  have hzx : IsClassicalMember p f M (g * z * g⁻¹) := by
    rw [hg]
    exact c.hz.conj g
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hxe : x = g * z * g⁻¹ :=
    Gaps.unique_involution_of_isClassicalMember h2 (c.hex M hM) hx hzx
  subst hxe
  have hshape_x : LocalShapeT p f 1 tY nY Ω (g * z * g⁻¹) := hshape.conj c.hΩ.conjInvariant g
  have hP1_x : LocalOddCentral Ω {g * z * g⁻¹} :=
    Gaps.localOddCentral_conj c.hΩ.conjInvariant g z c.hP1
  obtain ⟨dx⟩ := hshape_x.nonempty_dictT c.hY.ne_d4 c.hY.sc c.hΩ hM hzx
  let cx : ETCtx p f tY nY Ω M (g * z * g⁻¹) :=
    { hp2 := c.hp2, hq := c.hq, hΩ := c.hΩ, hex := c.hex, hK := hM, hz := hzx, hP1 := hP1_x,
      d := dx, hF := c.hF, hY := c.hY }
  exact ⟨cx⟩

end ETCtx

namespace ETCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {tY : StatedLieTag}
  {nY : ℕ} {N : Subgroup G} {x : G}

@[expose] def IsLayerMember (_ : ETCtx p f tY nY Ω N x) (L : Subgroup G) : Prop :=
  L ∈ centralizingMembers Ω {x} ∧ L ≠ N

theorem IsLayerMember.of_not_commutes (cx : ETCtx p f tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x}) (hne : L ≠ L')
    (hc : ¬ Commutes L L') : IsLayerMember cx L := by
  refine ⟨hL, ?_⟩
  rintro rfl
  exact hc (cx.commutes_K_of_ne hL' (fun h => hne h.symm))

theorem IsLayerMember.exists_fund {cx : ETCtx p f tY nY Ω N x} {L : Subgroup G}
    (hL : IsLayerMember cx L) :
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      locImg Ω x L = R.map cx.d.ψ :=
  cx.exists_fund_of_ne hL.1 hL.2

theorem exists_involution_of_fund (cx : ETCtx p f tY nY Ω N x) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x})
    {R : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) {w : G} (hw : IsClassicalMember p f L w) :
    ∃ r, Gaps.InvOf R r ∧ cx.d.ψ r = locElt Ω x w (le_centralizingLayer hL hw.mem) := by
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hL hw.mem
  have hmem : locElt Ω x w hwx ∈ R.map cx.d.ψ :=
    hLR ▸ locElt_mem_locImg (le_centralizingLayer hL) hw.mem
  obtain ⟨r, hrR, hr⟩ := hmem
  have h2 : orderOf (cx.d.ψ r) = 2 := by
    rw [hr]; exact orderOf_locElt hwx hw.orderOf_eq_two
  have hsq : r * r = 1 := by
    have h1 : cx.d.ψ (r * r) = 1 := by
      rw [map_mul]
      have := pow_orderOf_eq_one (cx.d.ψ r)
      rwa [h2, pow_two] at this
    exact cx.hY.central R hR (r * r) (R.mul_mem hrR hrR) (cx.d.ker_le h1)
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, map_one] at h2
    simp at h2
  exact ⟨r, ⟨hrR, orderOf_eq_prime (by rw [pow_two]; exact hsq) hr1⟩, hr⟩

theorem modelInvComm_of_commute (cx : ETCtx p f tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember p f L w) (hw' : IsClassicalMember p f L' w') (hc : Commute w w') :
    ∃ r r', Gaps.InvOf R r ∧ Gaps.InvOf R' r' ∧
      ⁅r, r'⁆ ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K ∧
      cx.d.ψ r = locElt Ω x w (le_centralizingLayer hL hw.mem) ∧
      cx.d.ψ r' = locElt Ω x w' (le_centralizingLayer hL' hw'.mem) := by
  obtain ⟨r, hr, hψr⟩ := cx.exists_involution_of_fund hL hR hLR hw
  obtain ⟨r', hr', hψr'⟩ := cx.exists_involution_of_fund hL' hR' hLR' hw'
  refine ⟨r, r', hr, hr', cx.d.ker_le ?_, hψr, hψr'⟩
  have hcomm : cx.d.ψ r * cx.d.ψ r' = cx.d.ψ r' * cx.d.ψ r := by
    rw [hψr, hψr', locElt_mul, locElt_mul]
    congr 1
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

omit [Finite G] in
theorem normalizes_of_conjSub (cx : ETCtx p f tY nY Ω N x) {L : Subgroup G}
    {R : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) {w : G} (hwx : w ∈ locLayer Ω x)
    {r : (modelUniv tY nY p f Fact.out).K} (hr : cx.d.ψ r = locElt Ω x w hwx)
    (hN : conjSub w L = L) : ∀ y ∈ R, r * y * r⁻¹ ∈ R := by
  refine Gaps.conj_mem_of_perfect (cx.hY.perfR R hR) r fun y hy => ?_
  have hmem : cx.d.ψ (r * y * r⁻¹) ∈ R.map cx.d.ψ := by
    have h1 : cx.d.ψ y ∈ locImg Ω x L := by
      rw [hLR]; exact ⟨y, hy, rfl⟩
    have h2 : cx.d.ψ (r * y * r⁻¹) ∈ locImg Ω x (conjSub w L) := by
      have := Gaps.locImg_conjSub_layer (Ω := Ω) (x := x) L ⟨w, hwx⟩
      rw [this]
      refine ⟨cx.d.ψ y, h1, ?_⟩
      simp only [map_mul, map_inv, hr]
      rfl
    rwa [hN, hLR] at h2
  obtain ⟨y', hy', hy'e⟩ := hmem
  refine ⟨y', hy', y'⁻¹ * (r * y * r⁻¹), cx.d.ker_le ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hy'e, inv_mul_cancel]

theorem modelAdj_of_adj (cx : ETCtx p f tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember p f L w) (hw' : IsClassicalMember p f L' w') (hne : L ≠ L')
    (hnc : ¬ Commutes L L') (hc : Commute w w') (hN : conjSub w' L = L) :
    Gaps.ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) R R' := by
  obtain ⟨r, r', hr, hr', hcen, hψr, hψr'⟩ :=
    cx.modelInvComm_of_commute hL hL' hR hR' hLR hLR' hw hw' hc
  refine ⟨fun h => hne (cx.eq_of_locImg_eq hL hL' (by rw [hLR, hLR', h])), ?_, r, r', hr, hr',
    hcen, ?_⟩
  · intro h
    exact hnc ((cx.commutes_iff_fund hL hL' hR hLR hLR').mpr h)
  · exact cx.normalizes_of_conjSub hR hLR (le_centralizingLayer hL' hw'.mem) hψr' hN

theorem sign_config (cx : ETCtx p f tY nY Ω N x)
    (hF : LayerGeom (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    {a b d : Subgroup G} {wa wb wd : G} (ha : a ∈ centralizingMembers Ω {x})
    (hb : b ∈ centralizingMembers Ω {x}) (hd : d ∈ centralizingMembers Ω {x})
    (hwa : IsClassicalMember p f a wa) (hwb : IsClassicalMember p f b wb)
    (hwd : IsClassicalMember p f d wd) (hab : a ≠ b) (hbd : b ≠ d)
    (hpair : ∃ W, LinearBlockStandardPair (GaloisField p f) W a b) (hnbd : ¬ Commutes b d)
    (had : Commutes a d) (hcab : Commute wa wb) (hcdb : Commute wd wb)
    (hna : conjSub wb a = a) (hnd : conjSub wb d = d) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W b d := by
  obtain ⟨W, hW⟩ := hpair
  have hnab : ¬ Commutes a b := not_commutes_of_linearBlockStandardPair hW
  have haL : IsLayerMember cx a := IsLayerMember.of_not_commutes cx ha hb hab hnab
  have hbL : IsLayerMember cx b := IsLayerMember.of_not_commutes cx hb hd hbd hnbd
  have hdL : IsLayerMember cx d := IsLayerMember.of_not_commutes cx hd hb hbd.symm
    (fun h => hnbd (Gaps.commutes_symm h))
  obtain ⟨Ra, hRa, haR⟩ := haL.exists_fund
  obtain ⟨Rb, hRb, hbR⟩ := hbL.exists_fund
  obtain ⟨Rd, hRd, hdR⟩ := hdL.exists_fund
  have hadjab : Gaps.ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) Ra Rb :=
    cx.modelAdj_of_adj ha hb hRa hRb haR hbR hwa hwb hab hnab hcab hna
  have hadjdb : Gaps.ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) Rd Rb :=
    cx.modelAdj_of_adj hd hb hRd hRb hdR hbR hwd hwb hbd.symm
      (fun h => hnbd (Gaps.commutes_symm h)) hcdb hnd
  have hcom : Commutes Ra Rd := (cx.commutes_iff_fund ha hd hRa haR hdR).mp had
  obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members cx.hP1 ha hb hW
  rw [haR, hbR] at hW'
  have hlift := hF.lift cx.d.ψ cx.d.ker_le Ra hRa Rb hRb ⟨W', hW'⟩
  obtain ⟨W₂, hW₂⟩ := hF.sign Ra hRa Rb hRb Rd hRd hadjab hadjdb hcom hlift
  exact cx.stdPair_of_fund hb hd hW₂ hbR hdR

variable {z : G} {K : Subgroup G}

theorem scenarioC (c : ETCtx p f tY nY Ω K z)
    (hF : LayerGeom (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 tY nY Ω z)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {J M : Subgroup G} (hJ : J ∈ Ω) (hM : M ∈ Ω) {wJ x : G} (hwJ : IsClassicalMember p f J wJ)
    (hwM : IsClassicalMember p f M x) (hKJ : Commutes K J) (hKM : Commutes K M)
    (hβM : Commutes β M) (hJM : Commutes J M) (hβJ : ¬ Commutes β J)
    (hnorm : conjSub t J = J) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β J := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hshape hM hwM
  obtain ⟨W, hW⟩ := hKβ
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
  have hβJne : β ≠ J := fun h => hnKβ (h ▸ hKJ)
  have hnormK : conjSub t K = K :=
    Gaps.conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  exact cx.sign_config hF (a := K) (b := β) (d := J) (wa := z) (wb := t) (wd := wJ)
    (mem_centralizingMembers_of_commutes c.hK hwM.mem hKM)
    (mem_centralizingMembers_of_commutes hβ hwM.mem hβM)
    (mem_centralizingMembers_of_commutes hJ hwM.mem hJM)
    c.hz ht hwJ hKne hβJne ⟨W, hW⟩ hβJ hKJ hzt
    (Gaps.commute_of_conjSub_eq' h2 (c.hex _ hJ) hwJ hnorm).symm hnormK hnorm

theorem exists_moved_layer_member (c : ETCtx p f tY nY Ω K z)
    (hF : LayerGeom (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 tY nY Ω z)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hM : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ N ∈ centralizingMembers Ω {z}, N ≠ K ∧ Commutes K N ∧ ¬ Commutes β N := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hM
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hshape hM hxM
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hKL := IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (Gaps.commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
  have hnormK : conjSub t K = K :=
    Gaps.conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadj : Gaps.ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) RK Rβ :=
    cx.modelAdj_of_adj hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  obtain ⟨S₁, hS₁, -, -, -, hc₁, -, hn₁, -⟩ := hF.perp2 RK hRK Rβ hRβ hadj hlinR
  obtain ⟨N₁, hN₁, -, hN₁R⟩ := cx.exists_member_of_fund hS₁
  have hKN₁ : Commutes K N₁ := (cx.commutes_iff_fund hKx hN₁ hRK hKR hN₁R).mpr hc₁
  have hβN₁ : ¬ Commutes β N₁ := fun h =>
    hn₁ ((cx.commutes_iff_fund hβx hN₁ hRβ hβR hN₁R).mp h)
  refine ⟨N₁, mem_centralizingMembers_of_commutes hN₁.1 c.hz.mem (Gaps.commutes_symm hKN₁),
    fun h => ?_, hKN₁, hβN₁⟩
  rw [h] at hKN₁
  exact not_commutes_self_of_mem c.hΩ c.hK hKN₁

theorem commutes_partner_of_centralizes (c : ETCtx p f tY nY Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hMFZ : Gaps.FundNoncentral p)
    (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f))
    (hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNt : N ≤ Subgroup.centralizer ({t} : Set G))
    (hNK : Commutes K N) : Commutes β N := by
  obtain ⟨z', hz'⟩ := c.hΩ.classical N hN.1
  exact commutes_partner_of_perfect_conj c.hp2 c.hq hMFZ hS3 c.hΩ hsingle c.hz hD4 c.hP1 hβ ht
    hKβ (commutator_eq_of_isClassicalMember hz') hNt (fun y' hy' x hx => hNK x hx y' hy')

end ETCtx

end CFSG.ClassicalInvolution.RouteD
