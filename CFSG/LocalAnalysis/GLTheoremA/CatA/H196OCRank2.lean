module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196OCCyc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196OCI194
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H196OC

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie isL2 ambiguousChev PSimple PQuot)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (map_glaPPrimeCoreOf_of_injective)
open CFSG.HardMathSupport.Timmesfeld.Balance (elemAbelian_subgroupOf)
open scoped Pointwise

theorem isChevSimple_of_mulEquiv {p : ℕ} {Q R : Type} [Group Q] [Group R] (e : Q ≃* R)
    (h : IsChevSimple p R) : IsChevSimple p Q := by
  rcases h with h | h
  · exact Or.inl (h196CatalogIs_of_mulEquiv e h)
  · exact Or.inr (h196CatalogIs_of_mulEquiv e h)

theorem innerAut_inf_centralizer_eq {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (e : MulAut S) :
    innerAut S ⊓ Subgroup.centralizer ({e} : Set (MulAut S)) =
      (fixSubgroup e).map (MulAut.conj : S →* MulAut S) := by
  ext y
  constructor
  · rintro ⟨⟨s, rfl⟩, hy⟩
    exact ⟨s, (CFSG.HardMathSupport.Dickson.I271.conj_mem_centralizer_iff hZ e s).1 hy, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, rfl⟩, (CFSG.HardMathSupport.Dickson.I271.conj_mem_centralizer_iff hZ e s).2 hs⟩

theorem commutator_sup_le_innerAut {S : Type} [Group S] {D : Subgroup (MulAut S)}
    (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) :
    ⁅innerAut S ⊔ D, innerAut S ⊔ D⁆ ≤ innerAut S := by
  haveI : (innerAut S).Normal := innerAut_normal S
  set π := QuotientGroup.mk' (innerAut S) with hπ
  have hmap : (innerAut S ⊔ D).map π = D.map π := by
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (by rw [hπ, QuotientGroup.ker_mk']),
      bot_sup_eq]
  have hcomm : ⁅D.map π, D.map π⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_bot, ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2
      (hD a ha b hb), map_one]
  have h1 : (⁅innerAut S ⊔ D, innerAut S ⊔ D⁆).map π = ⊥ := by
    rw [Subgroup.map_commutator, hmap, hcomm]
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
  exact h1

theorem prime_pow_eq_27 {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (h : p ^ f = 27) :
    p = 3 ∧ f = 3 := by
  have hp3 : p = 3 := by
    have hd : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 3 by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h]
      exact dvd_pow_self p hf.ne')
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    (show 3 ^ f = 3 ^ 3 by norm_num [h])⟩

theorem exists_eq_of_isL2 {n : ℕ} {ℓ : TauCeti.LieTypeIndex} (h : isL2 n ℓ) :
    ∃ q : TauCeti.PrimePower, ℓ = .A 1 q ∧ q.card = n := by
  cases ℓ
  case A r q =>
    rcases r with _ | _ | r
    · exact False.elim h
    · exact ⟨q, rfl, h⟩
    · exact False.elim h
  all_goals exact False.elim h

theorem isLTwoTwentySeven_of_catalogIs {X : Type} [Group X] (h : catalogIs X (onLie (isL2 27))) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven X := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic name => exact False.elim hi
  | lie d =>
    obtain ⟨ℓ, hv⟩ := d
    have hℓ : isL2 27 ℓ := hi
    obtain ⟨q, rfl, hq⟩ := exists_eq_of_isL2 hℓ
    obtain ⟨p, f, hpp, hff⟩ := q
    have hpf : p ^ f = 27 := (TauCeti.PrimePower.card_def _).symm.trans hq
    obtain ⟨rfl, rfl⟩ := prime_pow_eq_27 hpp hff hpf
    haveI : Fact (Nat.Prime 3) := ⟨hpp⟩
    refine ⟨GaloisField 3 3, inferInstance, inferInstance, ?_, ⟨(e.trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨3, 3, hpp, hff⟩ hv)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 3 3))⟩⟩
    rw [GaloisField.card 3 3 (by norm_num)]
    norm_num


theorem coreFree_rankTwo_lie {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hidx : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) (hchar : idx.1.characteristic = p)
    (h27 : ¬ (p = 3 ∧ CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven S))
    {D : Subgroup (MulAut S)} (hD : CFSG.Open.IsElemAbelian p D) (hcard : Nat.card D = p ^ 2)
    (hDI : D ⊓ innerAut S = ⊥) :
    GLAPPrimeCoreOf p (innerAut S ⊓ Subgroup.centralizer (D : Set (MulAut S))) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut S) := finite_mulAut S
  haveI : (innerAut S).Normal := innerAut_normal S
  have hZ : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.center_eq_bot_of_simple hS hnc
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    CFSG.HardMathSupport.Dickson.I271.conj_injective_of_center_bot hZ
  have hChev : IsChevSimple p S := Or.inl ⟨TauCeti.CFSGIndex.lie idx, hchar, hidx⟩
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨⟨e, heD⟩, he1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have he1 : e ≠ 1 := fun h => he1' (Subtype.ext h)
  have heord : orderOf e = p := orderOf_eq_prime (hD.2 e heD) he1
  have heI : e ∉ innerAut S := fun h => by
    have hmem : e ∈ D ⊓ innerAut S := ⟨heD, h⟩
    rw [hDI, Subgroup.mem_bot] at hmem
    exact he1 hmem
  have heM : e ∈ innerAut S ⊔ D := (le_sup_right : D ≤ innerAut S ⊔ D) heD
  have hDX : D ≤ (innerAut S ⊔ D) ⊓ Subgroup.centralizer ({e} : Set (MulAut S)) := fun d hd =>
    ⟨(le_sup_right : D ≤ innerAut S ⊔ D) hd,
      Subgroup.mem_centralizer_singleton_iff.2 (hDc d hd e heD)⟩
  have h27' : ¬ (p = 3 ∧ catalogIs S (onLie (isL2 27)) ∧ e ∉ innerAut S) := fun h =>
    h27 ⟨h.1, isLTwoTwentySeven_of_catalogIs h.2.1⟩
  have hXcore : GLAPPrimeCoreOf p ((innerAut S ⊔ D) ⊓
      Subgroup.centralizer ({e} : Set (MulAut S))) = ⊥ :=
    coreFree_cyc_simple hp hp2 hS hnc hChev heord le_sup_left (Subgroup.le_normalizer heM) h27'
  have hOC := (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.outerCentAll_holds
    (CFSG.Yardstones.Md42047359a2a.lieFamily idx.1)).2 S hS hnc idx rfl hidx p hp hp2 hchar.symm
    e heord heI
  have hcf : ∀ J : Subgroup (MulAut S),
      GLAPComponent p ((innerAut S ⊔ D) ⊓ Subgroup.centralizer ({e} : Set (MulAut S))) J →
        IsCompCoreFreeLocalType p D J := by
    intro J hJ
    have hJX : J ≤ (innerAut S ⊔ D) ⊓ Subgroup.centralizer ({e} : Set (MulAut S)) := hJ.1
    have hJI : J ≤ innerAut S :=
      calc J = ⁅J, J⁆ := (glaPComponent_perfect hJ).symm
        _ ≤ ⁅innerAut S ⊔ D, innerAut S ⊔ D⁆ :=
          Subgroup.commutator_mono (hJX.trans inf_le_left) (hJX.trans inf_le_left)
        _ ≤ innerAut S := commutator_sup_le_innerAut hDc
    have hJ0 : GLAPComponent p (innerAut S ⊓ Subgroup.centralizer ({e} : Set (MulAut S))) J :=
      glaPComponent_of_le hp hJ (le_inf hJI (hJX.trans inf_le_right))
        (inf_le_inf_right _ le_sup_left)
    obtain ⟨J₀, rfl⟩ : ∃ J₀ : Subgroup S, J = J₀.map (MulAut.conj : S →* MulAut S) :=
      ⟨J.comap MulAut.conj, (Subgroup.map_comap_eq_self hJI).symm⟩
    rw [innerAut_inf_centralizer_eq hZ e] at hJ0
    have hJ₀ : GLAPComponent p (fixSubgroup e) J₀ := (Y10F.glaPComponent_map_iff hp hinj).1 hJ0
    obtain ⟨eJ⟩ := nonempty_pSimple_equiv_map hp (MulAut.conj : S →* MulAut S) hJ₀ hJ
    have hJq : CFSG.Open.IsQuasisimple (PQuot p (J₀.map (MulAut.conj : S →* MulAut S))) :=
      isQuasisimple_pQuot_of_glaPComponent hp hJ
    have hchJ : IsChevSimple p (PSimple p (J₀.map (MulAut.conj : S →* MulAut S))) :=
      isChevSimple_of_mulEquiv eJ.symm (hOC.chev J₀ hJ₀)
    have heC : e ∈ Subgroup.centralizer
        ((J₀.map (MulAut.conj : S →* MulAut S) : Subgroup (MulAut S)) : Set (MulAut S)) :=
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.1 (hJX hy).2
    have heN := Subgroup.centralizer_le_normalizer _ heC
    have hbe : barAut p (J₀.map (MulAut.conj : S →* MulAut S)) ⟨e, heN⟩ = 1 := by
      refine MulEquiv.ext fun q => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      rw [barAut_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      show e * (y : MulAut S) * e⁻¹ = y
      rw [← Subgroup.mem_centralizer_iff.1 heC y y.2, mul_inv_cancel_right]
    set N := Subgroup.normalizer
      ((J₀.map (MulAut.conj : S →* MulAut S) : Subgroup (MulAut S)) : Set (MulAut S)) with hN
    set T : Subgroup ↥N := (D ⊓ N).subgroupOf N with hT
    set f : ↥T →* MulAut (barOf p (J₀.map (MulAut.conj : S →* MulAut S))) :=
      (barAut p (J₀.map (MulAut.conj : S →* MulAut S))).comp T.subtype with hf
    have hrange : f.range = autBar p D (J₀.map (MulAut.conj : S →* MulAut S)) := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    have hTcard : Nat.card T ≤ p ^ 2 := by
      rw [hT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, ← hcard]
      exact Subgroup.card_le_of_le inf_le_left
    let e0 : ↥T := ⟨⟨e, heN⟩, Subgroup.mem_subgroupOf.2 ⟨heD, heN⟩⟩
    have he0 : e0 ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      exact hbe
    have hord0 : orderOf e0 = p := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact heord
    have hker : p ≤ Nat.card f.ker :=
      calc p = Nat.card (Subgroup.zpowers e0) := by rw [Nat.card_zpowers, hord0]
        _ ≤ Nat.card f.ker := Subgroup.card_le_of_le (Subgroup.zpowers_le.2 he0)
    have hsplit : Nat.card T = Nat.card f.range * Nat.card f.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    have hcardA : Nat.card (autBar p D (J₀.map (MulAut.conj : S →* MulAut S))) ≤ p := by
      rw [← hrange]
      have h2 : Nat.card f.range * p ≤ p * p :=
        calc Nat.card f.range * p ≤ Nat.card f.range * Nat.card f.ker := Nat.mul_le_mul_left _ hker
          _ = Nat.card T := hsplit.symm
          _ ≤ p ^ 2 := hTcard
          _ = p * p := sq p
      exact Nat.le_of_mul_le_mul_right h2 hp.pos
    have hAel : CFSG.Open.IsElemAbelian p (autBar p D (J₀.map (MulAut.conj : S →* MulAut S))) :=
      (elemAbelian_subgroupOf inf_le_right (hD.mono inf_le_left)).map _
    have hL : p = 3 → catalogIs (PSimple p (J₀.map (MulAut.conj : S →* MulAut S)))
        (onLie (isL2 27)) → autBar p D (J₀.map (MulAut.conj : S →* MulAut S)) ≤
          innerAut (barOf p (J₀.map (MulAut.conj : S →* MulAut S))) := by
      rintro rfl h27J
      have h27J₀ : CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven (PSimple 3 J₀) :=
        isLTwoTwentySeven_of_catalogIs (h196CatalogIs_of_mulEquiv eJ h27J)
      rintro _ ⟨t, ht, rfl⟩
      have hdD : (t : MulAut S) ∈ D := (Subgroup.mem_subgroupOf.1 ht).1
      have hmapN : ∀ a ∈ N, J₀.map a.toMonoidHom ≤ J₀ := by
        intro a ha
        rintro _ ⟨s, hs, rfl⟩
        have h1 : a * MulAut.conj s * a⁻¹ ∈ J₀.map (MulAut.conj : S →* MulAut S) :=
          (Subgroup.mem_normalizer_iff.1 ha (MulAut.conj s)).1 ⟨s, hs, rfl⟩
        rw [CFSG.HardMathSupport.Dickson.I271.mulAut_mul_conj_mul_inv,
          Subgroup.mem_map_iff_mem hinj] at h1
        exact h1
      have htinv : (t : MulAut S)⁻¹ ∈ N := N.inv_mem t.2
      have hmapJ : J₀.map ((t : MulAut S)⁻¹).toMonoidHom = J₀ := by
        refine le_antisymm (hmapN _ htinv) fun s hs => ?_
        refine ⟨(t : MulAut S) s, hmapN _ t.2 ⟨s, hs, rfl⟩, ?_⟩
        simp
      have hd3 : ((t : MulAut S)⁻¹) ^ 3 = 1 := by rw [inv_pow, hD.2 _ hdD, inv_one]
      have hde : (t : MulAut S)⁻¹ * e = e * (t : MulAut S)⁻¹ :=
        (Commute.inv_left (hDc _ hdD e heD : Commute (t : MulAut S) e)).eq
      obtain ⟨i, hiJ, hi⟩ := hOC.l227 rfl J₀ hJ₀ h27J₀ _ hd3 hde hmapJ
      refine (inducesInnerMod_iff_barAut_mem_inner t.2).1
        ⟨MulAut.conj i⁻¹, ⟨i⁻¹, J₀.inv_mem hiJ, rfl⟩, fun y hy => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hy
      have hw := hi x hx
      have hc : (i * x * i⁻¹)⁻¹ ∈ J₀ :=
        J₀.inv_mem (J₀.mul_mem (J₀.mul_mem hiJ hx) (J₀.inv_mem hiJ))
      have hw' := CFSG.HardMathSupport.Dickson.I271.conj_mem_glaPPrimeCoreOf 3 J₀ hc hw
      have hmem : MulAut.conj ((i * x * i⁻¹)⁻¹ * (((t : MulAut S)⁻¹) x * (i * x * i⁻¹)⁻¹) *
          (i * x * i⁻¹)⁻¹⁻¹) ∈ GLAPPrimeCoreOf 3 (J₀.map (MulAut.conj : S →* MulAut S)) := by
        rw [← map_glaPPrimeCoreOf_of_injective 3 _ hinj]
        exact ⟨_, hw', rfl⟩
      have e1 : (MulAut.conj i⁻¹)⁻¹ * MulAut.conj x * MulAut.conj i⁻¹ =
          MulAut.conj (i * x * i⁻¹) := by
        simp only [map_mul, map_inv, inv_inv]
      have e2 : (t : MulAut S)⁻¹ * MulAut.conj x * (t : MulAut S) =
          MulAut.conj (((t : MulAut S)⁻¹) x) := by
        have h3 := CFSG.HardMathSupport.Dickson.I271.mulAut_mul_conj_mul_inv (t : MulAut S)⁻¹ x
        rwa [inv_inv] at h3
      have e3 : (MulAut.conj (i * x * i⁻¹))⁻¹ * MulAut.conj (((t : MulAut S)⁻¹) x) =
          MulAut.conj ((i * x * i⁻¹)⁻¹ * (((t : MulAut S)⁻¹) x * (i * x * i⁻¹)⁻¹) *
            (i * x * i⁻¹)⁻¹⁻¹) := by
        rw [← map_inv, ← map_mul]
        congr 1
        group
      rw [e1, e2, e3]
      exact hmem
    exact isCoreFreeLocalType_of_card_le hp hp2 hJq hchJ hAel hcardA hL
  have h194 := i194_of_le hp hDX hD le_rfl hcf
  rw [hXcore, le_bot_iff] at h194
  refine eq_bot_iff.2 fun w hw => ?_
  have hWle : GLAPPrimeCoreOf p (innerAut S ⊓ Subgroup.centralizer (D : Set (MulAut S))) ≤
      GLAPPrimeCoreOf p (((innerAut S ⊔ D) ⊓ Subgroup.centralizer ({e} : Set (MulAut S))) ⊓
        Subgroup.centralizer (D : Set (MulAut S))) := by
    apply le_GLAPPrimeCoreOf p
    · intro v hv
      have hv' := GLAPPrimeCoreOf_le p _ hv
      refine ⟨⟨(le_sup_left : innerAut S ≤ innerAut S ⊔ D) hv'.1, ?_⟩, hv'.2⟩
      exact Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hv'.2) e heD).symm
    · intro c hc v hv
      obtain ⟨⟨hcM, -⟩, hcD⟩ := hc
      have hcM' : c ∈ ((innerAut S ⊔ D : Subgroup (MulAut S)) : Set (MulAut S)) := hcM
      rw [Subgroup.normal_mul] at hcM'
      obtain ⟨i, hi, d, hd, rfl⟩ := hcM'
      have hdC : d ∈ Subgroup.centralizer (D : Set (MulAut S)) :=
        Subgroup.mem_centralizer_iff.2 fun h hh => hDc h hh d hd
      have hiD : i ∈ Subgroup.centralizer (D : Set (MulAut S)) := by
        have := (Subgroup.centralizer (D : Set (MulAut S))).mul_mem hcD
          ((Subgroup.centralizer (D : Set (MulAut S))).inv_mem hdC)
        simpa using this
      have h1 := GLAPPrimeCoreOf_conj p _ (Subgroup.mem_inf.2 ⟨hi, hiD⟩) hv
      have hvD := (GLAPPrimeCoreOf_le p _ hv).2
      have hdv : d * v * d⁻¹ = v := by
        rw [(Subgroup.mem_centralizer_iff.1 hvD) d hd, mul_inv_cancel_right]
      have e1 : i * d * v * (i * d)⁻¹ = i * v * i⁻¹ :=
        calc i * d * v * (i * d)⁻¹ = i * (d * v * d⁻¹) * i⁻¹ := by group
          _ = i * v * i⁻¹ := by rw [hdv]
      rw [e1]
      exact h1
    · exact not_dvd_card_GLAPPrimeCoreOf p _
  have h2 := hWle hw
  rwa [h194] at h2


end CFSG.LocalAnalysis.GLTheoremA.H196OC

end
