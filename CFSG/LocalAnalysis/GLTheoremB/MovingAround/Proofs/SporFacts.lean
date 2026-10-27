module

public import CFSG.HardMathSupport.Solomon.Proving.Fi22Facts
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeKFact
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input1919
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.BigPrimes
public import CFSG.Sporadic.HeldB.OuterCent
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporHeNine

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporFacts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut IsFiTwentyTwo Fi22Facts)
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem pRank_le_of_forall [Finite G] {p m : ℕ} {H : Subgroup G}
    (h : ∀ E : Subgroup G, E ≤ H → CFSG.Open.IsElemAbelian p E → ∀ k : ℕ,
      Nat.card E = p ^ k → k ≤ m) :
    CFSG.Open.pRank p H ≤ m := by
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro k ⟨E, hEH, hE, hcard⟩
  exact h E hEH hE k hcard

theorem card_dvd_of_le_inner [Finite G] {E : Subgroup (MulAut G)}
    (hE : E ≤ (MulAut.conj : G →* MulAut G).range) : Nat.card E ∣ Nat.card G := by
  have hmap : (E.comap (MulAut.conj : G →* MulAut G)).map MulAut.conj = E := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hE]
  rw [← hmap]
  exact (Subgroup.card_map_dvd _ _).trans (Subgroup.card_subgroup_dvd_card _)

theorem isPGroup_zpowers_of_pow_eq_one {p : ℕ} {g : G} (hg : g ^ p = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  rintro ⟨x, hx⟩
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hg, one_zpow]

theorem eq_bot_or_eq_of_isSubnormal {L D : Subgroup G} (h : CFSG.Open.IsSubnormal L D)
    (hD : IsSimpleGroup D) : L = ⊥ ∨ L = D := by
  induction h with
  | refl => exact Or.inr rfl
  | @step H M K hHM hn _ ih =>
    rcases ih hD with rfl | rfl
    · exact Or.inl (le_bot_iff.1 hHM)
    · haveI := hn
      rcases hD.eq_bot_or_eq_top_of_normal (H.subgroupOf M) with h | h
      · left
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact h.eq_bot_of_le hHM
      · right
        exact le_antisymm hHM (Subgroup.subgroupOf_eq_top.1 h)

theorem eq_bot_of_perfect_of_isSolvable [Group.IsSolvable G] {H : Subgroup G}
    (hH : ⁅H, H⁆ = H) : H = ⊥ := by
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.2 hH
  by_contra hne
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
  exact Group.IsPerfect.not_isSolvable H inferInstance

theorem isQuasisimple_of_isSimpleGroup {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hnc : ∃ a b : Q, a * b ≠ b * a) : CFSG.Open.IsQuasisimple Q := by
  obtain ⟨a, b, hab⟩ := hnc
  have hcen : Subgroup.center Q = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a)
  refine ⟨?_, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      apply hab
      have hc : ⁅a, b⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  · have e : Q ⧸ Subgroup.center Q ≃* Q :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup

theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  refine ⟨?_, ?_⟩
  · haveI : Group.IsPerfect A := ⟨h.1⟩
    exact (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective).commutator_eq_top
  · haveI := h.2
    exact (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)).symm.isSimpleGroup

theorem nontrivial_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    Nontrivial Q := by
  haveI := h.2
  by_contra hQ
  rw [not_nontrivial_iff_subsingleton] at hQ
  have : Subsingleton (Q ⧸ Subgroup.center Q) := QuotientGroup.mk_surjective.subsingleton
  exact not_nontrivial (Q ⧸ Subgroup.center Q) inferInstance

theorem centralizer_eq_of_zpowers_eq {Q : Type*} [Group Q] {a b : Q}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set Q) = Subgroup.centralizer {b} := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, h,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

end Generic

section Layer

variable {G : Type*} [Group G] [Finite G]

theorem glaPPrimeCore_eq_bot {p : ℕ} (hp : p.Prime) {X D : Subgroup G} (hDX : D ≤ X)
    (hDn : (D.subgroupOf X).Normal) (hDs : IsSimpleGroup D) (hpD : p ∣ Nat.card D)
    (hC : IsPGroup p (X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G)) :
    GLAPPrimeCore p ↥X = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  show CFSG.pPrimeCore p ↥X = ⊥
  unfold CFSG.pPrimeCore
  rw [sSup_eq_bot]
  rintro N ⟨hNn, hNc⟩
  set N' : Subgroup G := N.map X.subtype with hN'
  have hN'X : N' ≤ X := Subgroup.map_subtype_le N
  have hcardN' : Nat.card N' = Nat.card N :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hmemN' : ∀ {g : G} (hg : g ∈ X), g ∈ N' ↔ (⟨g, hg⟩ : ↥X) ∈ N := by
    intro g hg
    constructor
    · rintro ⟨m, hm, hmg⟩
      have : m = ⟨g, hg⟩ := Subtype.ext hmg
      exact this ▸ hm
    · intro h
      exact ⟨_, h, rfl⟩
  have hNconj : ∀ {x n : G}, x ∈ X → n ∈ N' → x * n * x⁻¹ ∈ N' := by
    intro x n hx hn
    have hnX : n ∈ X := hN'X hn
    rw [hmemN' (X.mul_mem (X.mul_mem hx hnX) (X.inv_mem hx))]
    have := hNn.conj_mem ⟨n, hnX⟩ ((hmemN' hnX).1 hn) ⟨x, hx⟩
    exact this
  have hDconj : ∀ {x d : G}, x ∈ X → d ∈ D → x * d * x⁻¹ ∈ D := by
    intro x d hx hd
    have h := hDn.conj_mem ⟨d, hDX hd⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨x, hx⟩
    rwa [Subgroup.mem_subgroupOf] at h
  have hND : N' ⊓ D = ⊥ := by
    have hnorm : ((N' ⊓ D).subgroupOf D).Normal := by
      refine ⟨fun n hn d => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hn1, hn2⟩ := hn
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ⟨hNconj (hDX d.2) hn1, D.mul_mem (D.mul_mem d.2 hn2) (D.inv_mem d.2)⟩
    haveI := hnorm
    rcases hDs.eq_bot_or_eq_top_of_normal ((N' ⊓ D).subgroupOf D) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact h.eq_bot_of_le inf_le_right
    · exfalso
      have hDN : D ≤ N' := (Subgroup.subgroupOf_eq_top.1 h).trans inf_le_left
      have h1 : Nat.card D ∣ Nat.card N := hcardN' ▸ Subgroup.card_dvd_of_le hDN
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hNc (hpD.trans h1)
  have hNC : N' ≤ X ⊓ Subgroup.centralizer (D : Set G) := by
    refine le_inf hN'X fun n hn => Subgroup.mem_centralizer_iff.2 fun d hd => ?_
    have hc : ⁅n, d⁆ ∈ N' ⊓ D := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        have h1 : d * n⁻¹ * d⁻¹ ∈ N' := hNconj (hDX hd) (N'.inv_mem hn)
        have := N'.mul_mem hn h1
        simpa only [mul_assoc] using this
      · rw [commutatorElement_def]
        exact D.mul_mem (hDconj (hN'X hn) hd) (D.inv_mem hd)
    rw [hND, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc.symm
  have hNp : IsPGroup p N' := hC.to_le hNC
  rcases hNp.card_eq_or_dvd with h | h
  · rw [hcardN'] at h
    exact Subgroup.card_eq_one.1 h
  · rw [hcardN'] at h
    exact absurd h ((Nat.Prime.coprime_iff_not_dvd hp).1 hNc)

theorem glaPComponent_eq_of_simple_normal {p : ℕ} {X D L : Subgroup G} (hDX : D ≤ X)
    (hDn : (D.subgroupOf X).Normal) (hDs : IsSimpleGroup D)
    (hsol : Group.IsSolvable (↥X ⧸ D.subgroupOf X)) (hL : GLAPComponent p X L) : L = D := by
  have hperf : ⁅L, L⁆ = L := glaPComponent_perfect hL
  obtain ⟨hLX, hsn, hcomp, -⟩ := hL
  have hLD : L ≤ D := by
    set π := QuotientGroup.mk' (D.subgroupOf X)
    have hperf' : ⁅(L.subgroupOf X).map π, (L.subgroupOf X).map π⁆ =
        (L.subgroupOf X).map π := by
      rw [← Subgroup.map_commutator, ← subgroupOf_commutator hLX hLX, hperf]
    have hbot := eq_bot_of_perfect_of_isSolvable hperf'
    intro l hl
    have hmem : (⟨l, hLX hl⟩ : ↥X) ∈ D.subgroupOf X := by
      rw [← QuotientGroup.ker_mk' (D.subgroupOf X)]
      rw [MonoidHom.mem_ker]
      have : π ⟨l, hLX hl⟩ ∈ (L.subgroupOf X).map π :=
        Subgroup.mem_map_of_mem π (by rwa [Subgroup.mem_subgroupOf])
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rwa [Subgroup.mem_subgroupOf] at hmem
  have hsnD : CFSG.Open.IsSubnormal L D := isSubnormal_of_le_of_le hsn hLD hDX
  rcases eq_bot_or_eq_of_isSubnormal hsnD hDs with h | h
  · exfalso
    subst h
    have hnt := nontrivial_of_isQuasisimple hcomp.2.2
    have hb : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) =
        ⊥ := by
      rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
    rw [hb] at hnt
    exact (not_nontrivial_iff_subsingleton.2 inferInstance) hnt
  · exact h

theorem glaPLayer_eq {p : ℕ} (hp : p.Prime) {X D : Subgroup G} (hDX : D ≤ X)
    (hDn : (D.subgroupOf X).Normal) (hDs : IsSimpleGroup D) (hDnc : ∃ a b : D, a * b ≠ b * a)
    (hpD : p ∣ Nat.card D) (hC : IsPGroup p (X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G))
    (hsol : Group.IsSolvable (↥X ⧸ D.subgroupOf X)) : GLAPLayer p X = D := by
  have hcore := glaPPrimeCore_eq_bot hp hDX hDn hDs hpD hC
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  have hDcomp : GLAPComponent p X D := by
    refine ⟨hDX, CFSG.Open.IsSubnormal.step hDX hDn (CFSG.Open.IsSubnormal.refl X), ?_, ?_⟩
    · refine ⟨le_top, ?_, ?_⟩
      · have hn : ((D.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).Normal :=
          hDn.map _ (QuotientGroup.mk'_surjective _)
        exact CFSG.Open.IsSubnormal.step le_top (hn.subgroupOf ⊤) (CFSG.Open.IsSubnormal.refl ⊤)
      · have e : ↥D ≃* ↥((D.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))) :=
          (Subgroup.subgroupOfEquivOfLe hDX).symm.trans
            (Subgroup.equivMapOfInjective _ _ hinj)
        exact isQuasisimple_of_mulEquiv e (isQuasisimple_of_isSimpleGroup hDs hDnc)
    · intro J hJD hJX heq
      have hJX' : J ≤ X := hJD.le.trans hDX
      have h1 : J.subgroupOf X = D.subgroupOf X := Subgroup.map_injective hinj heq
      rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hJX', inf_eq_left.2 hDX] at h1
      exact hJD.ne h1
  unfold GLAPLayer
  show sSup {L | GLAPComponent p X L} = D
  exact le_antisymm (sSup_le fun L hL => (glaPComponent_eq_of_simple_normal hDX hDn hDs hsol hL).le)
    (le_sSup hDcomp)

end Layer

section Fi22Seven

theorem input7_Fi22_holds : Input7_Fi22 := by
  intro X _ _ hX
  obtain ⟨-, hfac, -, hinn⟩ := CFSG.HardMathSupport.Solomon.Proving.fi22Facts_holds X hX
  have hinner : ∀ φ : MulAut X, IsPGroup 5 (Subgroup.zpowers φ) →
      φ ∈ (MulAut.conj : X →* MulAut X).range := fun φ hφ => by
    obtain ⟨k, hk⟩ := hinn φ hφ
    exact ⟨k, hk.symm⟩
  refine ⟨hinner, fun A _ => ?_⟩
  apply pRank_le_of_forall
  intro E _ hE k hk
  have hEi : E ≤ (MulAut.conj : X →* MulAut X).range := fun φ hφ =>
    hinner φ (isPGroup_zpowers_of_pow_eq_one (hE.2 φ hφ))
  have hdvd : 5 ^ k ∣ Nat.card X := by
    rw [← hk]
    exact card_dvd_of_le_inner hEi
  have h2 := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').1 hdvd
  omega

end Fi22Seven

section Fi22Lines

open CFSG.RankThree.Native CFSG.Monster.B.Fischer in
theorem exists_conj_line {y : fi22P} (hy : orderOf y = 5) :
    ∃ (g : fi22P) (j : Fin 6),
      Subgroup.zpowers ((g * y * g⁻¹ : fi22P) : Equiv.Perm (Fin 3510)) =
        Subgroup.zpowers (fi22FiveLine j) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPy : IsPGroup 5 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨T, hT⟩ := hPy.exists_le_sylow
  obtain ⟨S, hS⟩ := fi22FiveQ_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq fi22P T S
  have hyT : y ∈ T := hT (Subgroup.mem_zpowers y)
  have hconj : MulAut.conj g y ∈ (S : Subgroup fi22P) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hyT
  have hmem : ((g * y * g⁻¹ : fi22P) : Equiv.Perm (Fin 3510)) ∈ fi22FiveQ := by
    rw [hS, MulAut.conj_apply] at hconj
    exact Subgroup.mem_subgroupOf.1 hconj
  have hord : orderOf ((g * y * g⁻¹ : fi22P) : Equiv.Perm (Fin 3510)) = 5 := by
    rw [Subgroup.orderOf_coe, ← MulAut.conj_apply]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y).trans hy
  have hin : Subgroup.zpowers ((g * y * g⁻¹ : fi22P) : Equiv.Perm (Fin 3510)) ∈
      {H : Subgroup (Equiv.Perm (Fin 3510)) | H ≤ fi22FiveQ ∧ Nat.card H = 5} :=
    ⟨Subgroup.zpowers_le.2 hmem, by rw [Nat.card_zpowers, hord]⟩
  rw [fi22FiveQ_lines.1] at hin
  obtain ⟨j, hj⟩ := hin
  exact ⟨g, j, hj.symm⟩

end Fi22Lines

section Fi22Five

open CFSG.RankThree.Native CFSG.Monster.B.Fischer in
theorem input14_21_holds : Input14_21 := by
  intro K _ _ hK x hx
  obtain ⟨e⟩ := hK
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have β' : CFSG.Blueprint.NativeSporadic.Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := β
  let θ : K ≃* fi22P := (e.trans β'.symm).trans fi22PermEquiv
  have hy : orderOf (θ x) = 5 := by
    rw [← hx]
    exact orderOf_injective θ.toMonoidHom θ.injective x
  obtain ⟨g, j, hgj⟩ := exists_conj_line hy
  let φ : K ≃* fi22P := θ.trans (MulAut.conj g)
  let f : K →* Equiv.Perm (Fin 3510) := fi22P.subtype.comp φ.toMonoidHom
  have hfinj : Function.Injective f := Subtype.val_injective.comp φ.injective
  have hfP : ∀ k, f k ∈ fi22P := fun k => (φ k).2
  have hfrange : f.range = fi22P := by
    ext s
    constructor
    · rintro ⟨k, rfl⟩
      exact hfP k
    · intro hs
      refine ⟨φ.symm ⟨s, hs⟩, ?_⟩
      show ((φ (φ.symm ⟨s, hs⟩) : fi22P) : Equiv.Perm (Fin 3510)) = s
      rw [MulEquiv.apply_symm_apply]
  have hfx : f x = ((g * θ x * g⁻¹ : fi22P) : Equiv.Perm (Fin 3510)) := rfl
  have hcz : Subgroup.centralizer ({f x} : Set (Equiv.Perm (Fin 3510))) =
      Subgroup.centralizer {fi22FiveLine j} :=
    centralizer_eq_of_zpowers_eq (by rw [hfx, hgj])
  have hcent : ∀ k : K, k ∈ Subgroup.centralizer ({x} : Set K) ↔
      f k ∈ Subgroup.centralizer ({fi22FiveLine j} : Set (Equiv.Perm (Fin 3510))) := by
    intro k
    rw [← hcz, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← map_mul, ← map_mul, hfinj.eq_iff]
  have hcentP : ∀ k : K, k ∈ Subgroup.centralizer ({x} : Set K) → f k ∈ fi22FiveC j := by
    intro k hk
    have h1 : f k ∈ Subgroup.centralizer {fi22FiveLine j} ⊓ fi22P :=
      Subgroup.mem_inf.2 ⟨(hcent k).1 hk, hfP k⟩
    rw [← fi22FiveC_inf_P j] at h1
    exact (Subgroup.mem_inf.1 h1).1
  let X : Subgroup K := Subgroup.centralizer ({x} : Set K)
  let D : Subgroup K := (fi22FiveD j).comap f
  have hDX : D ≤ X := fun k hk =>
    (hcent k).2 (fi22FiveC_le_centralizer_line j (fi22FiveD_le_C j hk))
  have hDn : (D.subgroupOf X).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' : f n ∈ fi22FiveD j := hn
    show f ((c * n * c⁻¹ : X) : K) ∈ fi22FiveD j
    have hcC : f c ∈ fi22FiveC j := hcentP c c.2
    have hnC : f n ∈ fi22FiveC j := fi22FiveD_le_C j hn'
    have hrw : f ((c * n * c⁻¹ : X) : K) = ⁅f c, f n⁆ * f n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, commutatorElement_def]
      group
    rw [hrw]
    exact (fi22FiveD j).mul_mem (Subgroup.commutator_mem_commutator hcC hnC) hn'
  have hDmap : D.map f = fi22FiveD j := by
    rw [Subgroup.map_comap_eq, hfrange]
    exact inf_eq_right.2 (fi22FiveD_le_P j)
  let eD : ↥D ≃* ↥(fi22FiveD j) :=
    (Subgroup.equivMapOfInjective D f hfinj).trans (MulEquiv.subgroupCongr hDmap)
  haveI := fi22FiveD_isSimpleGroup j
  have hDs : IsSimpleGroup D := eD.isSimpleGroup
  have hDnc : ∃ a b : D, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := fi22FiveD_nonabelian j
    refine ⟨eD.symm ⟨a, ha⟩, eD.symm ⟨b, hb⟩, fun h => hab ?_⟩
    have h' := congrArg eD h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact congrArg Subtype.val h'
  have hcardD : Nat.card D = 60 := by
    rw [Nat.card_congr eD.toEquiv, card_fi22FiveD j]
  have hC : IsPGroup 5 (X ⊓ Subgroup.centralizer (D : Set K) : Subgroup K) := by
    rintro ⟨k, hk⟩
    obtain ⟨hkX, hkD⟩ := Subgroup.mem_inf.1 hk
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    have hfk : f k ∈ Subgroup.centralizer (fi22FiveD j : Set (Equiv.Perm (Fin 3510))) ⊓
        (fi22FiveC j ⊓ fi22P) := by
      refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_inf.2 ⟨hcentP k hkX, hfP k⟩⟩
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      rw [← hDmap] at hd
      obtain ⟨d', hd', rfl⟩ := hd
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hkD d' hd']
    rw [fi22FiveCentDP_eq j] at hfk
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hfk
    have h5 : f (k ^ 5) = f 1 := by
      rw [map_pow, ← hn, map_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        fi22FiveLine_pow_five j, one_zpow]
    exact hfinj h5
  have hXmap : X.map f = Subgroup.centralizer {fi22FiveLine j} ⊓ fi22P := by
    ext s
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact Subgroup.mem_inf.2 ⟨(hcent k).1 hk, hfP k⟩
    · intro hs
      obtain ⟨hs1, hs2⟩ := Subgroup.mem_inf.1 hs
      rw [← hfrange] at hs2
      obtain ⟨k, rfl⟩ := hs2
      exact ⟨k, (hcent k).2 hs1, rfl⟩
  have hcardX : Nat.card X = 600 := by
    rw [← Subgroup.card_map_of_injective hfinj, hXmap, ← fi22FiveC_inf_P j,
      card_fi22FiveC_inf_P j]
  have hsol : Group.IsSolvable (↥X ⧸ D.subgroupOf X) := by
    apply CFSG.GroupTheory.groups_order_below_sixty_solvable
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf X)
    rw [hcardX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv, hcardD] at h1
    omega
  have hL : GLAPLayer 5 X = D :=
    glaPLayer_eq (by norm_num) hDX hDn hDs hDnc (by rw [hcardD]; norm_num) hC hsol
  show IsAltType 5 ↥(GLAPLayer 5 X)
  rw [hL]
  obtain ⟨eA⟩ :=
    CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
      (G := ↥(fi22FiveD j)) (card_fi22FiveD j)
  exact ⟨eD.trans eA⟩

end Fi22Five

section AutRankGeneric

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (OffPair SporadicOnePair)

theorem isElemAbelian_map {A B : Type*} [Group A] [Group B] {p : ℕ} {E : Subgroup A}
    (hE : CFSG.Open.IsElemAbelian p E) (f : A →* B) : CFSG.Open.IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    have hxy : x * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]

theorem center_eq_bot_of_quasisimple_quot {Y : Type*} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) :
    Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  haveI := hY.2
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Y ⧸ Subgroup.center Y))
    with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative (Y ⧸ Subgroup.center Y) :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative (Y ⧸ Subgroup.center Y) inferInstance

theorem pRank_aut_le_two_of_autRankLe2 {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y)
    (h : CFSG.HardMathSupport.Dickson.I271.AutRankLe2 p (Y ⧸ Subgroup.center Y)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤ 2 := by
  have hinj := CFSG.GH74.KGroups.inducedHom_injective (K := Y) ⟨hY.1⟩
  apply pRank_le_of_forall
  intro E _ hE k hk
  have h1 := h (E.map CFSG.GH74.KGroups.inducedHom) (isElemAbelian_map hE _)
  rw [Subgroup.card_map_of_injective hinj, hk] at h1
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1

theorem pRank_aut_le_two_of_offPair {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type*} [Group Y]
    [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) {name : TauCeti.SporadicName}
    (hnot : ¬ SporadicOnePair name p) {C : Type} [Group C] (hOff : OffPair name C)
    (f : (Y ⧸ Subgroup.center Y) ≃* C)
    (hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤ 2 :=
  pRank_aut_le_two_of_autRankLe2 hp hY
    (CFSG.HardMathSupport.Dickson.I271.autRankLe2_of_offPair hp hp2 hnot hOff f
      (center_eq_bot_of_quasisimple_quot hY) hout)

end AutRankGeneric

section AutRankM23

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem pRank_aut_M23 {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic .M23).Group) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) ≤ 2 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .M23 ≃*
      (TauCeti.CFSGIndex.sporadic .M23).Group := b
  let f := e.trans b'.symm
  have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv]
    exact CFSG.Sporadic.Schreier.at_m23_schreier.1
  exact pRank_aut_le_two_of_offPair Nat.prime_three (by norm_num) hY (by decide)
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_M23 f hout

end AutRankM23

section AutRankHS

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem pRank_aut_HS {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic .HS).Group) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) ≤ 2 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .HS ≃*
      (TauCeti.CFSGIndex.sporadic .HS).Group := b
  let f := e.trans b'.symm
  have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv]
    exact CFSG.Sporadic.Schreier.HS_outer_card_le_two.1
  exact pRank_aut_le_two_of_offPair Nat.prime_three (by norm_num) hY (by decide)
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_HS f hout

end AutRankHS

section AutRankM24

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem pRank_aut_M24 {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic .M24).Group) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) ≤ 2 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .M24 ≃*
      (TauCeti.CFSGIndex.sporadic .M24).Group := b
  let f := e.trans b'.symm
  have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv]
    exact CFSG.AGLEmbedding.card_outer_M24.le.trans (by norm_num)
  exact pRank_aut_le_two_of_offPair Nat.prime_three (by norm_num) hY (by decide)
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_M24 f hout

end AutRankM24

section AutRankHe

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem pRank_aut_He {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic .He).Group) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) ≤ 2 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .He ≃*
      (TauCeti.CFSGIndex.sporadic .He).Group := b
  let f := e.trans b'.symm
  have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv]
    exact CFSG.Sporadic.Schreier.AT_He_Schreier.1
  exact pRank_aut_le_two_of_offPair Nat.prime_three (by norm_num) hY (by decide)
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_He f hout

end AutRankHe

section AutRankSuz

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem pRank_aut_Suz {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut Y)) ≤ 2 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .Suz ≃*
      (TauCeti.CFSGIndex.sporadic .Suz).Group := b
  let f := e.trans b'.symm
  have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv,
      CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1]
  exact pRank_aut_le_two_of_offPair (by norm_num) (by norm_num) hY (by decide)
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_Suz f hout

end AutRankSuz

section AutRankM

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem pRank_aut_M {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :
    CFSG.Open.pRank 13 (⊤ : Subgroup (MulAut Y)) ≤ 2 := by
  haveI := hY.2
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .M ≃*
      (TauCeti.CFSGIndex.sporadic .M).Group := b
  let f := e.trans b'.symm
  have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) = 1 :=
    CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple f
  obtain ⟨eG⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple f
  have hpair := CFSG.AGLEmbedding.Norton.MON11_13.hasNoncommPair_thirteen_of_mulEquiv_Gmat eG
  have hcard : Nat.card (Y ⧸ Subgroup.center Y) = CFSG.Open.monsterOrder :=
    (Nat.card_congr eG.toEquiv).trans CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  have h4 : ¬ 13 ^ 4 ∣ Nat.card (Y ⧸ Subgroup.center Y) := by
    rw [hcard]
    norm_num [CFSG.Open.monsterOrder]
  apply pRank_aut_le_two_of_autRankLe2 (by norm_num) hY
  exact CFSG.HardMathSupport.Dickson.I271.autRankLe2_of_noCube (by norm_num)
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.noElemAbelianCubeAut_of_noncomm (by norm_num)
      (by norm_num) (center_eq_bot_of_quasisimple_quot hY) (by omega) h4 hpair)

end AutRankM

section AutRank

theorem inputSporAutRank_holds : Claims1116.InputSporAutRank := by
  intro Y _ _ p s hps hY _ hsp
  obtain ⟨e⟩ := hsp
  rcases hps with ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact pRank_aut_M23 hY e
  · exact pRank_aut_HS hY e
  · exact pRank_aut_M24 hY e
  · exact pRank_aut_He hY e
  · exact pRank_aut_Suz hY e
  · exact pRank_aut_M hY e

end AutRank

section SuzFive

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem inputSuzFive_holds : Claims1116.InputSuzFive := by
  intro Y _ _ hY hcore hsp
  obtain ⟨e⟩ := hsp
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Suz ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group := b
  have b'' : CFSG.Blueprint.NativeSporadic.Carrier .Suz ≃*
      (TauCeti.CFSGIndex.sporadic .Suz).Group := b
  let f : (Y ⧸ Subgroup.center Y) ≃* CFSG.Blueprint.NativeSporadic.Suz := e.trans b'.symm
  let f' : (Y ⧸ Subgroup.center Y) ≃* CFSG.Blueprint.NativeSporadic.Carrier .Suz :=
    e.trans b''.symm
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  have hdvd : Nat.card (Subgroup.center Y) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier CFSG.Blueprint.NativeSporadic.Suz) :=
    CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier (Q := Y)
      (S := CFSG.Blueprint.NativeSporadic.Suz) inferInstance f
  have hM := CFSG.Sporadic.Recognition.SuzMultiplier.card_griessHopfMultiplier_Suz
    Certificates.certificate15030 Certificates.certificate15031
    Certificates.certificate15033 Certificates.certificate15034
    Certificates.certificate15035
  have h6 : Nat.card (Subgroup.center Y) ∣ 6 := by
    rcases hM with h | h <;> rw [h] at hdvd
    · exact hdvd.trans (by norm_num)
    · exact hdvd
  have hcop : Nat.Coprime 5 (Nat.card (Subgroup.center Y)) :=
    Nat.Coprime.coprime_dvd_right h6 (by norm_num)
  have hZ : Subgroup.center Y = ⊥ := by
    have hle : Subgroup.center Y ≤ CFSG.pPrimeCore 5 Y := by
      unfold CFSG.pPrimeCore
      exact le_sSup ⟨inferInstance, hcop⟩
    have hcore' : CFSG.pPrimeCore 5 Y = ⊥ := hcore
    rw [hcore'] at hle
    exact le_bot_iff.1 hle
  refine ⟨hZ, fun P hP => ?_⟩
  let eY : Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .Suz :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans f'
  have hout : Nat.card (Outer Y) = 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eY).toEquiv]
    exact CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1
  have hle : P ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner Y :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.le_inner_of_isPGroup (by rw [hout]; norm_num) hP
  refine ⟨?_, hle⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have hdvdY : Nat.card P ∣ Nat.card Y := card_dvd_of_le_inner hle
  have hcardY : Nat.card Y = 448345497600 :=
    (Nat.card_congr eY.toEquiv).trans CFSG.Sporadic.Suz.card_Suz
  rw [hcardY, hk] at hdvdY
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h3 : 5 ^ 3 ∣ 448345497600 := (pow_dvd_pow 5 (by omega)).trans hdvdY
    norm_num at h3
  rw [hk]
  calc 5 ^ k ≤ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 25 := by norm_num

end SuzFive

section HeGeneric

theorem eq_top_or_le_center_of_normal {Z : Type} [Group Z] (hZ : CFSG.Open.IsQuasisimple Z)
    (W : Subgroup Z) [W.Normal] : W = ⊤ ∨ W ≤ Subgroup.center Z := by
  by_cases h : W = ⊤
  · exact Or.inl h
  · exact Or.inr (l119_normal_le_center hZ h)

theorem eq_or_le_center_of_isSubnormal {G : Type} [Group G] {Q X : Subgroup G}
    (hX : CFSG.Open.IsQuasisimple ↥X) (h : CFSG.Open.IsSubnormal Q X) :
    Q = X ∨ Q ≤ (Subgroup.center ↥X).map X.subtype := by
  induction h with
  | refl => exact Or.inl rfl
  | @step H M K hHM hn _ ih =>
    rcases ih hX with rfl | hM
    · haveI := hn
      rcases eq_top_or_le_center_of_normal hX (H.subgroupOf M) with h | h
      · exact Or.inl (le_antisymm hHM (Subgroup.subgroupOf_eq_top.1 h))
      · right
        intro x hx
        exact ⟨⟨x, hHM hx⟩, h (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    · exact Or.inr (hHM.trans hM)

theorem glaPComponent_eq_of_isQuasisimple {G : Type} [Group G] {p : ℕ} {X Q : Subgroup G}
    (hX : CFSG.Open.IsQuasisimple ↥X) (hQ : GLAPComponent p X Q) : Q = X := by
  have hperf : ⁅Q, Q⁆ = Q := glaPComponent_perfect hQ
  obtain ⟨hQX, hsn, hcomp, -⟩ := hQ
  rcases eq_or_le_center_of_isSubnormal hX hsn with h | h
  · exact h
  · exfalso
    have hcomm : ⁅Q, Q⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨a, ha, rfl⟩ := h hx
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 ha ⟨y, hQX hy⟩)
    rw [hperf] at hcomm
    subst hcomm
    have hnt := nontrivial_of_isQuasisimple hcomp.2.2
    have hb : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) =
        ⊥ := by
      rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
    rw [hb] at hnt
    exact (not_nontrivial_iff_subsingleton.2 inferInstance) hnt

theorem glaPPrimeCore_eq_bot_of_isQuasisimple {Z : Type} [Group Z] [Finite Z] {p : ℕ}
    (hp : p.Prime) (hZ : CFSG.Open.IsQuasisimple Z) (hc : IsPGroup p (Subgroup.center Z))
    (hpZ : p ∣ Nat.card Z) : GLAPPrimeCore p Z = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p Z)) := CFSG.pPrimeCore_coprime_card
  rcases eq_top_or_le_center_of_normal hZ (GLAPPrimeCore p Z) with h | h
  · exfalso
    rw [h, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpZ
  · rcases (hc.to_le h).card_eq_or_dvd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exact absurd h1 ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop)

theorem nonempty_barZ3_equiv {G : Type} [Group G] {Q : Subgroup G}
    (hcore : GLAPPrimeCore 3 ↥Q = ⊥) :
    Nonempty (Prop126b.barZ3 Q ≃* (↥Q ⧸ Subgroup.center ↥Q)) :=
  ⟨l119_centerQuot_equiv
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot)⟩

theorem psl2_equiv_closure_set {F : Type} [Field F] [Finite F] {N : ℕ}
    (E : Fin N ≃ Projectivization F (Fin 2 → F)) (S : Set (Equiv.Perm (Fin N)))
    (hS : ∀ s ∈ S, ∃ A : Matrix.SpecialLinearGroup (Fin 2) F, ∀ i, E (s i) = A • E i)
    (P : Subgroup (Equiv.Perm (Fin N))) (hP : P = Subgroup.closure S)
    (hcard : Nat.card P = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* P) := by
  have hinj := CFSG.GH74.KGroups.PSL2.permHom_injective E (F := F)
  have hrange : P = (CFSG.GH74.KGroups.PSL2.permHom E :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →* _).range := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [hP, Subgroup.closure_le]
      intro s hs
      obtain ⟨A, hA⟩ := hS s hs
      exact ⟨_, CFSG.GH74.KGroups.PSL2.permHom_mk_eq E A s hA⟩
    · rw [hcard, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)⟩

theorem glaPComponent_self_of_isQuasisimple {G : Type*} [Group G] {p : ℕ} {X : Subgroup G}
    (hX : CFSG.Open.IsQuasisimple ↥X) (hcore : GLAPPrimeCore p ↥X = ⊥) : GLAPComponent p X X := by
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  have htop : (X.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  refine ⟨le_rfl, CFSG.Open.IsSubnormal.refl X, ⟨le_top, ?_, ?_⟩, ?_⟩
  · rw [htop]
    exact CFSG.Open.IsSubnormal.refl ⊤
  · have e : ↥X ≃* ↥((X.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))) :=
      (Subgroup.subgroupOfEquivOfLe le_rfl).symm.trans (Subgroup.equivMapOfInjective _ _ hinj)
    exact isQuasisimple_of_mulEquiv e hX
  · intro J hJX _ heq
    have h1 : J.subgroupOf X = X.subgroupOf X := Subgroup.map_injective hinj heq
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hJX.le, inf_idem] at h1
    exact hJX.ne h1

end HeGeneric

section HeThreeBSmall

open CFSG.GH74.KGroups CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He CFSG.Sporadic.HeldB
open scoped Matrix

@[expose] def heBPi : Equiv.Perm (Fin 8) := List.formPerm [4, 6, 5, 7]

@[expose] def heBM1 : Matrix.SpecialLinearGroup (Fin 2) (PF 7) :=
  ⟨!![(PF.ofNat' 3), (PF.ofNat' 6); (PF.ofNat' 0), (PF.ofNat' 5)], by
    rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def heBM2 : Matrix.SpecialLinearGroup (Fin 2) (PF 7) :=
  ⟨!![(PF.ofNat' 0), (PF.ofNat' 2); (PF.ofNat' 3), (PF.ofNat' 1)], by
    rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def heBM3 : Matrix.SpecialLinearGroup (Fin 2) (PF 7) :=
  ⟨!![(PF.ofNat' 1), (PF.ofNat' 1); (PF.ofNat' 4), (PF.ofNat' 5)], by
    rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def heBTau1 : Equiv.Perm (Fin 8) := List.formPerm [1, 4, 7] * List.formPerm [2, 3, 5]

@[expose] def heBTau2 : Equiv.Perm (Fin 8) := List.formPerm [0, 5, 7] * List.formPerm [1, 2, 3]

@[expose] def heBTau3 : Equiv.Perm (Fin 8) := List.formPerm [0, 7, 2] * List.formPerm [4, 5, 6]

theorem permOrId_heThreeSigmaB_zero :
    permOrId 8 (heThreeSigmaB.getD 0 #[]) = 1 := by
  have h := (permChk_spec (bigDataB.gens 0 (by norm_num)).2.2.2.1).1
  refine Equiv.ext fun x => Fin.ext ?_
  rw [← h x]
  revert x
  decide

theorem permOrId_heThreeSigmaB_one :
    permOrId 8 (heThreeSigmaB.getD 1 #[]) = heBTau1 := by
  have h := (permChk_spec (bigDataB.gens 1 (by norm_num)).2.2.2.1).1
  refine Equiv.ext fun x => Fin.ext ?_
  rw [← h x]
  revert x
  decide

theorem permOrId_heThreeSigmaB_two :
    permOrId 8 (heThreeSigmaB.getD 2 #[]) = heBTau2 := by
  have h := (permChk_spec (bigDataB.gens 2 (by norm_num)).2.2.2.1).1
  refine Equiv.ext fun x => Fin.ext ?_
  rw [← h x]
  revert x
  decide

theorem permOrId_heThreeSigmaB_three :
    permOrId 8 (heThreeSigmaB.getD 3 #[]) = heBTau3 := by
  have h := (permChk_spec (bigDataB.gens 3 (by norm_num)).2.2.2.1).1
  refine Equiv.ext fun x => Fin.ext ?_
  rw [← h x]
  revert x
  decide

theorem heBM1_act : ∀ i : Fin 8, ∃ c : PF 7,
    c • ((heBM1 : Matrix (Fin 2) (Fin 2) (PF 7)) *ᵥ PSL2.vecP L27.enum (heBPi i)) =
      PSL2.vecP L27.enum (heBPi (heBTau1 i)) := by
  decide +kernel

theorem heBM2_act : ∀ i : Fin 8, ∃ c : PF 7,
    c • ((heBM2 : Matrix (Fin 2) (Fin 2) (PF 7)) *ᵥ PSL2.vecP L27.enum (heBPi i)) =
      PSL2.vecP L27.enum (heBPi (heBTau2 i)) := by
  decide +kernel

theorem heBM3_act : ∀ i : Fin 8, ∃ c : PF 7,
    c • ((heBM3 : Matrix (Fin 2) (Fin 2) (PF 7)) *ᵥ PSL2.vecP L27.enum (heBPi i)) =
      PSL2.vecP L27.enum (heBPi (heBTau3 i)) := by
  decide +kernel

@[expose] noncomputable def heBLine : Fin 8 ≃ Projectivization (PF 7) (Fin 2 → PF 7) :=
  (heBPi : Fin 8 ≃ Fin 8).trans (PSL2.ptEquiv L27.enum L27.enum_bij)

theorem heBLine_act (A : Matrix.SpecialLinearGroup (Fin 2) (PF 7)) (g : Equiv.Perm (Fin 8))
    (h : ∀ i : Fin 8, ∃ c : PF 7, c • ((A : Matrix (Fin 2) (Fin 2) (PF 7)) *ᵥ
      PSL2.vecP L27.enum (heBPi i)) = PSL2.vecP L27.enum (heBPi (g i))) :
    ∀ i, heBLine (g i) = A • heBLine i := by
  intro i
  simp only [heBLine, Equiv.trans_apply]
  rw [PSL2.ptEquiv_apply, PSL2.ptEquiv_apply]
  unfold PSL2.pt
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  exact h i

theorem nonempty_psl_equiv_heThreeXB :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7) ≃* heThreeXB.originalSubgroup) := by
  refine psl2_equiv_closure_set heBLine _ ?_ _ heThreeXB_eq ?_
  · rintro _ ⟨j, hj, rfl⟩
    interval_cases j
    · exact ⟨1, fun i => by rw [permOrId_heThreeSigmaB_zero, one_smul]; rfl⟩
    · exact ⟨heBM1, by rw [permOrId_heThreeSigmaB_one]; exact heBLine_act heBM1 _ heBM1_act⟩
    · exact ⟨heBM2, by rw [permOrId_heThreeSigmaB_two]; exact heBLine_act heBM2 _ heBM2_act⟩
    · exact ⟨heBM3, by rw [permOrId_heThreeSigmaB_three]; exact heBLine_act heBM3 _ heBM3_act⟩
  · rw [card_heThreeXB, L27.card_psl_F]

end HeThreeBSmall

section HeThreeCent

open CFSG.GH74.KGroups CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
  CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

theorem factorization_504_three : (504 : ℕ).factorization 3 = 2 := by
  rw [show (504 : ℕ) = 3 ^ 2 * 56 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem psl27_noncomm :
    ∃ x y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7), x * y ≠ y * x := by
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [PF.card]; norm_num)
  by_contra h
  push Not at h
  haveI : IsMulCommutative (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7)) := ⟨⟨h⟩⟩
  have hc : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7)) = 168 := L27.card_psl_F
  let _ : CommGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7)) :=
    { (inferInstance : Group (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7))) with
      mul_comm := h }
  have hp := (IsSimpleGroup.prime_card (α := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7)))
  rw [hc] at hp
  norm_num at hp

theorem heThreeB_component :
    ∃ D : Subgroup (Equiv.Perm (Fin 8330)),
      Nonempty (↥D ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7)) ∧
        (∀ Q : Subgroup (Equiv.Perm (Fin 8330)),
          GLAPComponent 3 (centralizerIn heP (bOf heThreeWordsB)) Q → Q = D) ∧
        GLAPComponent 3 (centralizerIn heP (bOf heThreeWordsB)) D ∧
        ∀ c ∈ centralizerIn heP (bOf heThreeWordsB), Nat.Coprime (orderOf c) 3 → c ∈ D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := grpOf heThreeWordsB 4 with hCdef
  have hCeq : C = centralizerIn heP (bOf heThreeWordsB) :=
    (heThree_theta bigDataB (by norm_num) heThreeXB heThreeXB_eq radB
      (by rw [card_cent_B, card_heThreeXB])).1
  set ρ := restrictHom (delta_injective bigDataB) C (grpOf_stab bigDataB) with hρ
  have hrange : ρ.range = heThreeXB.originalSubgroup :=
    restrict_range bigDataB heThreeXB heThreeXB_eq
  have hcardC : Nat.card C = 504 := by rw [hCeq, card_cent_B]
  have hcardX : Nat.card heThreeXB.originalSubgroup = 168 := card_heThreeXB
  set V := ρ.ker with hV
  have hcardV : Nat.card V = 3 := by
    have h1 := Subgroup.card_mul_index ρ.ker
    rw [Subgroup.index_ker, hrange, hcardX, hcardC, ← hV] at h1
    omega
  set bB : ↥C := ⟨bOf heThreeWordsB, b_mem_grpOf (by norm_num)⟩ with hbB
  have hbV : bB ∈ V := by
    rw [hV, MonoidHom.mem_ker]
    exact (restrictHom_eq_one_iff _ _ _).2 (bOf_fix bigDataB)
  have hbcent : bB ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro c
    have hc : (c : Equiv.Perm (Fin 8330)) ∈ centralizerIn heP (bOf heThreeWordsB) := hCeq ▸ c.2
    exact Subtype.ext (mem_centralizerIn.1 hc).2
  have hordb : orderOf bB = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_bOf bigDataB
  have hVz : V = Subgroup.zpowers bB := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hbV) ?_).symm
    rw [Nat.card_zpowers, hordb, hcardV]
  have hVcent : V ≤ Subgroup.center ↥C := by
    rw [hVz, Subgroup.zpowers_le]
    exact hbcent
  have hVp : IsPGroup 3 V := IsPGroup.of_card (n := 1) (by rw [hcardV, pow_one])
  haveI : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hVcent b.2) a)⟩⟩
  have hexp : ∀ x : ↥C, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ^ 3 = 1 := by
    rintro x ⟨k, hk⟩
    have hx' : (x : Equiv.Perm (Fin 8330)) ∈ centralizerIn heP (bOf heThreeWordsB) := by
      rw [← hCeq]
      exact x.2
    have hxP : (x : Equiv.Perm (Fin 8330)) ∈ heP := (mem_centralizerIn.1 hx').1
    have h1 : (⟨x, hxP⟩ : heP) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h2 := he_pow_three h1
    exact Subtype.ext (by simpa using congrArg Subtype.val h2)
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥C) := inferInstance
  have hP9 : Nat.card (P : Subgroup ↥C) = 9 := by
    rw [Sylow.card_eq_multiplicity, hcardC, factorization_504_three]
    norm_num
  have hVP : V ≤ P := hVp.le_sylow_of_normal P
  obtain ⟨x, hxP, hxV⟩ : ∃ x ∈ (P : Subgroup ↥C), x ∉ V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le h
    rw [hP9, hcardV] at this
    omega
  have hx3 : x ^ 3 = 1 := hexp x (by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
  have hx1 : x ≠ 1 := fun h => hxV (h ▸ V.one_mem)
  have hordx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  set K' := Subgroup.zpowers x with hK'
  have hcardK' : Nat.card K' = 3 := by rw [Nat.card_zpowers, hordx]
  have hK'P : K' ≤ P := Subgroup.zpowers_le.2 hxP
  have hVK' : V ⊓ K' = ⊥ := by
    have hd : Nat.card ↥(V ⊓ K') ∣ 3 := by
      rw [← hcardK']
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact Subgroup.card_eq_one.1 h
    · exfalso
      have heq : V ⊓ K' = K' := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hcardK'])
      exact hxV ((heq ▸ inf_le_left : K' ≤ V) (Subgroup.mem_zpowers x))
  have hsupP : V ⊔ K' = P := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hVP hK'P)
    rw [hP9]
    have hd1 : Nat.card ↥(V ⊔ K') ∣ 9 := by
      rw [← hP9]
      exact Subgroup.card_dvd_of_le (sup_le hVP hK'P)
    have hd2 : 3 ∣ Nat.card ↥(V ⊔ K') := by
      rw [← hcardV]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hlt : Nat.card V < Nat.card ↥(V ⊔ K') := by
      apply Subgroup.card_lt_of_lt
      refine lt_of_le_of_ne le_sup_left fun h => hxV ?_
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [hcardV] at hlt
    have h9 : Nat.card ↥(V ⊔ K') ≤ 9 := Nat.le_of_dvd (by norm_num) hd1
    interval_cases h : Nat.card ↥(V ⊔ K') <;> omega
  obtain ⟨H, hVH, hsupH⟩ := (CFSG.Quasithin.gaschutz hVp P).2 ⟨K', hK'P, hVK', hsupP⟩
  set ψ := ρ.comp H.subtype with hψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have hmem : (h : ↥C) ∈ V ⊓ H := ⟨hh, h.2⟩
    rw [hVH, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).2 (Subtype.ext hmem)
  have hψrange : ψ.range = heThreeXB.originalSubgroup := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype, ← hrange, MonoidHom.range_eq_map,
      ← hsupH, Subgroup.map_sup]
    have hVmap : V.map ρ = ⊥ := (Subgroup.map_eq_bot_iff V).2 le_rfl
    rw [hVmap, bot_sup_eq]
  let eH : ↥H ≃* ↥heThreeXB.originalSubgroup :=
    (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange)
  obtain ⟨eX⟩ := nonempty_psl_equiv_heThreeXB
  have hHn : H.Normal := by
    refine ⟨fun h hh c => ?_⟩
    have hc : c ∈ V ⊔ H := hsupH ▸ Subgroup.mem_top c
    obtain ⟨v, hv, h₀, hh₀, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hc
    have hvc : ∀ g : ↥C, v * g = g * v := fun g => (Subgroup.mem_center_iff.1 (hVcent hv) g).symm
    have : v * h₀ * h * (v * h₀)⁻¹ = h₀ * h * h₀⁻¹ := by
      calc v * h₀ * h * (v * h₀)⁻¹ = v * (h₀ * h * h₀⁻¹) * v⁻¹ := by group
        _ = h₀ * h * h₀⁻¹ * v * v⁻¹ := by rw [hvc (h₀ * h * h₀⁻¹)]
        _ = h₀ * h * h₀⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem hh₀ hh) (H.inv_mem hh₀)
  set D : Subgroup (Equiv.Perm (Fin 8330)) := H.map C.subtype with hD
  have hDC : D ≤ C := Subgroup.map_subtype_le H
  have hDsub : D.subgroupOf C = H := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_iff_mem C.subtype_injective
  let eDH : ↥D ≃* ↥H := (H.equivMapOfInjective C.subtype C.subtype_injective).symm
  have hDs : IsSimpleGroup ↥D := by
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [PF.card]; norm_num)
    exact (eDH.trans (eH.trans eX.symm)).isSimpleGroup
  have hcardD : Nat.card D = 168 := by
    rw [Nat.card_congr (eDH.trans eH).toEquiv, hcardX]
  have hDn : (D.subgroupOf C).Normal := hDsub ▸ hHn
  have hsol : Group.IsSolvable (↥C ⧸ D.subgroupOf C) := by
    apply CFSG.GroupTheory.groups_order_below_sixty_solvable
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf C)
    rw [hcardC, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, hcardD] at h1
    omega
  have hDnc : ∃ a b : ↥D, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := psl27_noncomm
    refine ⟨(eDH.trans (eH.trans eX.symm)).symm a, (eDH.trans (eH.trans eX.symm)).symm b,
      fun h => hab ?_⟩
    have := congrArg (eDH.trans (eH.trans eX.symm)) h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  refine ⟨D, ⟨eDH.trans (eH.trans eX.symm)⟩, fun Q hQ => ?_, ?_, ?_⟩
  · rw [← hCeq] at hQ
    exact glaPComponent_eq_of_simple_normal hDC hDn hDs hsol hQ
  · rw [← hCeq]
    exact Claims126.glaPComponent_of_simple_normal Nat.prime_three hDC hDn hDs hDnc
      (by rw [hcardD]; norm_num)
  · intro c hc hcop
    rw [← hCeq] at hc
    set c' : ↥C := ⟨c, hc⟩ with hc'
    have hc'top : c' ∈ V ⊔ H := hsupH ▸ Subgroup.mem_top c'
    obtain ⟨v, hv, h, hh, hvh⟩ := Subgroup.mem_sup_of_normal_left.1 hc'top
    have hcomm : Commute v h := ((Subgroup.mem_center_iff.1 (hVcent hv) h)).symm
    set n := orderOf c' with hn
    have hcopn : Nat.Coprime n 3 := by rw [hn, Subgroup.orderOf_mk]; exact hcop
    have hvn : v ^ n = 1 := by
      have h1 : v ^ n * h ^ n = 1 := by
        rw [← hcomm.mul_pow, hvh, hn, pow_orderOf_eq_one]
      have h2 : v ^ n ∈ V ⊓ H := by
        refine Subgroup.mem_inf.2 ⟨V.pow_mem hv n, ?_⟩
        have : v ^ n = (h ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact H.inv_mem (H.pow_mem hh n)
      rw [hVH, Subgroup.mem_bot] at h2
      exact h2
    have hv3 : v ^ 3 = 1 := by
      have := pow_card_eq_one' (G := V) (x := ⟨v, hv⟩)
      rw [hcardV] at this
      exact congrArg Subtype.val this
    have hv1 : v = 1 := by
      have hd : orderOf v ∣ Nat.gcd n 3 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hvn) (orderOf_dvd_of_pow_eq_one hv3)
      rw [hcopn.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd
      exact hd
    rw [hv1, one_mul] at hvh
    have hc'H : c' ∈ H := hvh ▸ hh
    exact ⟨c', hc'H, rfl⟩

theorem heThreeB_barZ3 {Q : Subgroup (Equiv.Perm (Fin 8330))}
    (hQ : GLAPComponent 3 (centralizerIn heP (bOf heThreeWordsB)) Q) :
    IsLpType 2 7 (Prop126b.barZ3 Q) := by
  obtain ⟨D, ⟨eD⟩, hD, -, -⟩ := heThreeB_component
  have hQD := hD Q hQ
  subst hQD
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (PF 7)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [PF.card]; norm_num)
  have hs : IsSimpleGroup ↥Q := eD.isSimpleGroup
  have hnc : ∃ x y : ↥Q, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := psl27_noncomm
    refine ⟨eD.symm x, eD.symm y, fun h => hxy ?_⟩
    have := congrArg eD h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  have h3 : 3 ∣ Nat.card ↥Q := by
    rw [Nat.card_congr eD.toEquiv, L27.card_psl_F]
    norm_num
  obtain ⟨e₁⟩ := Claims126.barZ3_simple hs hnc h3
  exact ⟨PF 7, inferInstance, inferInstance, PF.card,
    ⟨(e₁.trans eD).trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (PF 7))⟩⟩

theorem heThreeA_barZ3 {Q : Subgroup (Equiv.Perm (Fin 8330))}
    (hQ : GLAPComponent 3 (centralizerIn heP (bOf heThreeWordsA)) Q) :
    IsAltType 7 (Prop126b.barZ3 Q) := by
  rw [← heTcQ_eq] at hQ
  obtain ⟨-, hqs, hZ3, ⟨eA⟩⟩ := heTc_spec
  have hq : CFSG.Open.IsQuasisimple ↥heTcQ := ⟨hqs.1.commutator_eq_top, hqs.2.1⟩
  have hQX := glaPComponent_eq_of_isQuasisimple hq hQ
  subst hQX
  have hc : IsPGroup 3 (Subgroup.center ↥heTcQ) := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have h3 : 3 ∣ Nat.card ↥heTcQ := by rw [card_heTcQ]; norm_num
  have hcore := glaPPrimeCore_eq_bot_of_isQuasisimple Nat.prime_three hq hc h3
  obtain ⟨e⟩ := nonempty_barZ3_equiv hcore
  exact ⟨e.trans eA⟩

theorem heThreeA_component :
    GLAPComponent 3 (centralizerIn heP (bOf heThreeWordsA)) heTcQ := by
  obtain ⟨-, hqs, hZ3, -⟩ := heTc_spec
  have hq : CFSG.Open.IsQuasisimple ↥heTcQ := ⟨hqs.1.commutator_eq_top, hqs.2.1⟩
  have hc : IsPGroup 3 (Subgroup.center ↥heTcQ) := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have h3 : 3 ∣ Nat.card ↥heTcQ := by rw [card_heTcQ]; norm_num
  have hcore := glaPPrimeCore_eq_bot_of_isQuasisimple Nat.prime_three hq hc h3
  rw [← heTcQ_eq]
  exact glaPComponent_self_of_isQuasisimple hq hcore

end HeThreeCent

section HeCent

open CFSG.GH74.KGroups CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem inputHeCent_holds : Prop126b.InputHeCent := by
  intro Y _ _ K hq hHe b hbN hb3 hnc Q hQ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hHe
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have β' : CFSG.Blueprint.NativeSporadic.He ≃* (TauCeti.CFSGIndex.sporadic .He).Group := β
  have β'' : CFSG.Blueprint.NativeSporadic.Carrier .He ≃*
      (TauCeti.CFSGIndex.sporadic .He).Group := β
  let f₀ : (↥K ⧸ Subgroup.center ↥K) ≃* CFSG.Blueprint.NativeSporadic.He := e.trans β'.symm
  have hq' : CFSG.IsQuasisimple ↥K :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq⟩
  have hZ : Subgroup.center ↥K = ⊥ :=
    CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate ↥K hq' ⟨f₀⟩
  let eQ : ↥K ≃* (↥K ⧸ Subgroup.center ↥K) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let eK : ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He := eQ.trans (e.trans β''.symm)
  let eP : ↥K ≃* heP := eK.trans heEquivP
  have hout : Nat.card (Outer ↥K) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eK).toEquiv]
    exact CFSG.Sporadic.Schreier.AT_He_Schreier.1
  have hbmem : ∀ k : Y, k ∈ K ↔ b * k * b⁻¹ ∈ K := Subgroup.mem_normalizer_iff.1 hbN
  let βb : MulAut ↥K :=
    { toFun := fun k => ⟨b * k * b⁻¹, (hbmem k).1 k.2⟩
      invFun := fun k => ⟨b⁻¹ * k * b, (hbmem _).2 (by simpa [mul_assoc] using k.2)⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hβ : ∀ k : ↥K, ((βb k : ↥K) : Y) = b * k * b⁻¹ := fun k => rfl
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hβ3 : βb ^ 3 = 1 := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply, hβ, hβ, hβ]
    calc b * (b * (b * (k : Y) * b⁻¹) * b⁻¹) * b⁻¹ = b * (b * b) * k * (b * (b * b))⁻¹ := by
          group
      _ = k := by rw [← pow_three, hb3']; group
  have hβ1 : βb ≠ 1 := by
    intro h
    obtain ⟨q, hqK, hbq⟩ := hnc
    apply hbq
    have h1 : b * q * b⁻¹ = q := by
      have := congrArg (fun φ : MulAut ↥K => ((φ ⟨q, hqK⟩ : ↥K) : Y)) h
      exact this
    calc b * q = b * q * b⁻¹ * b := by group
      _ = q * b := by rw [h1]
  have hcop : Nat.Coprime 3 (Nat.card (Outer ↥K)) :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.coprime_of_le_two Nat.prime_three (by norm_num)
      Nat.card_pos.ne' hout
  have hin : Subgroup.zpowers βb ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.le_inner_of_isPGroup hcop
      (isPGroup_zpowers_of_pow_eq_one hβ3)
  obtain ⟨k₀, hk₀⟩ := hin (Subgroup.mem_zpowers βb)
  have hconj : ∀ k : ↥K, k₀ * k * k₀⁻¹ = βb k := fun k => by rw [← hk₀]; rfl
  have hk₀3 : k₀ ^ 3 = 1 := by
    have hc : k₀ ^ 3 ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : MulAut.conj (k₀ ^ 3) = 1 := by rw [map_pow, hk₀, hβ3]
      have h2 : k₀ ^ 3 * g * (k₀ ^ 3)⁻¹ = g := by
        have := congrArg (fun φ : MulAut ↥K => φ g) h1
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * k₀ ^ 3 = k₀ ^ 3 * g * (k₀ ^ 3)⁻¹ * k₀ ^ 3 := by rw [h2]
        _ = k₀ ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hk₀1 : k₀ ≠ 1 := by
    rintro rfl
    apply hβ1
    rw [← hk₀, map_one]
  have hordk : orderOf k₀ = 3 := orderOf_eq_prime hk₀3 hk₀1
  have hcent : ∀ k : ↥K, (k : Y) ∈ Subgroup.centralizer ({b} : Set Y) ↔ k * k₀ = k₀ * k := by
    intro k
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : βb k = k := Subtype.ext (by
        rw [hβ]
        calc b * (k : Y) * b⁻¹ = k * b * b⁻¹ := by rw [h]
          _ = k := by group)
      rw [← hconj] at h1
      calc k * k₀ = k₀ * k * k₀⁻¹ * k₀ := by rw [h1]
        _ = k₀ * k := by group
    · intro h
      have h1 : k₀ * k * k₀⁻¹ = k := by rw [← h]; group
      rw [hconj] at h1
      have h2 : b * (k : Y) * b⁻¹ = k := by rw [← hβ]; exact congrArg Subtype.val h1
      calc (k : Y) * b = b * k * b⁻¹ * b := by rw [h2]
        _ = b * k := by group
  have hordP : orderOf ((eP k₀ : heP) : Equiv.Perm (Fin 8330)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hordk]
  have hQK : Q ≤ K := hQ.1.trans inf_le_left
  have key : ∀ (ws : List (List ℤ)) (c : Equiv.Perm (Fin 8330)) (hc : c ∈ heP),
      ((eP k₀ : heP) : Equiv.Perm (Fin 8330)) = c * bOf ws * c⁻¹ →
      ∃ F : ↥K →* Equiv.Perm (Fin 8330), Function.Injective F ∧
        ((K ⊓ Subgroup.centralizer ({b} : Set Y)).subgroupOf K).map F =
          centralizerIn heP (bOf ws) := by
    intro ws c hc hcx
    let φ : ↥K ≃* heP := eP.trans (MulAut.conj (⟨c, hc⟩ : heP)⁻¹)
    have hφ : ((φ k₀ : heP) : Equiv.Perm (Fin 8330)) = bOf ws := by
      show c⁻¹ * ((eP k₀ : heP) : Equiv.Perm (Fin 8330)) * c = bOf ws
      rw [hcx]
      group
    refine ⟨heP.subtype.comp φ.toMonoidHom, Subtype.val_injective.comp φ.injective, ?_⟩
    ext s
    constructor
    · intro hs
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hs
      rw [Subgroup.mem_subgroupOf] at hk
      have hkc := (hcent k).1 (Subgroup.mem_inf.1 hk).2
      refine mem_centralizerIn.2 ⟨(φ k).2, ?_⟩
      show ((φ k : heP) : Equiv.Perm (Fin 8330)) * bOf ws =
        bOf ws * ((φ k : heP) : Equiv.Perm (Fin 8330))
      rw [← hφ]
      have := congrArg (fun z => ((φ z : heP) : Equiv.Perm (Fin 8330))) hkc
      simpa only [map_mul, Subgroup.coe_mul] using this
    · intro hs
      obtain ⟨hsP, hsc⟩ := mem_centralizerIn.1 hs
      refine Subgroup.mem_map.2 ⟨φ.symm ⟨s, hsP⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_inf.2 ⟨(φ.symm ⟨s, hsP⟩).2, (hcent _).2 ?_⟩
        apply φ.injective
        apply Subtype.ext
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul, hφ]
        exact hsc
      · show ((φ (φ.symm ⟨s, hsP⟩) : heP) : Equiv.Perm (Fin 8330)) = s
        rw [MulEquiv.apply_symm_apply]
  have transport : ∀ (ws : List (List ℤ)) (c : Equiv.Perm (Fin 8330)) (hc : c ∈ heP),
      ((eP k₀ : heP) : Equiv.Perm (Fin 8330)) = c * bOf ws * c⁻¹ →
      ∃ Q' : Subgroup (Equiv.Perm (Fin 8330)), GLAPComponent 3 (centralizerIn heP (bOf ws)) Q' ∧
        Nonempty (Prop126b.barZ3 Q ≃* Prop126b.barZ3 Q') := by
    intro ws c hc hcx
    obtain ⟨F, hFinj, hFmap⟩ := key ws c hc hcx
    refine ⟨(Q.subgroupOf K).map F, ?_, ⟨Claims126.barZ3Congr
      ((Subgroup.subgroupOfEquivOfLe hQK).symm.trans
        ((Q.subgroupOf K).equivMapOfInjective F hFinj))⟩⟩
    rw [← hFmap]
    refine glaPComponent_map Nat.prime_three F ?_
      (Prop126b.glaPComponent_subgroupOf Nat.prime_three inf_le_left hQ)
    rw [(MonoidHom.ker_eq_bot_iff F).2 hFinj, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  rcases three_conj_cases (eP k₀).2 hordP with ⟨c, hc, hcx⟩ | ⟨c, hc, hcx⟩
  ·
    obtain ⟨Q', hQ', ⟨eQ'⟩⟩ := transport heThreeWordsA c hc hcx
    obtain ⟨eA⟩ := heThreeA_barZ3 hQ'
    exact Or.inr ⟨eQ'.trans eA⟩
  ·
    obtain ⟨Q', hQ', ⟨eQ'⟩⟩ := transport heThreeWordsB c hc hcx
    obtain ⟨Fld, hF1, hF2, hF3, ⟨eL⟩⟩ := heThreeB_barZ3 hQ'
    exact Or.inl ⟨Fld, hF1, hF2, hF3, ⟨eQ'.trans eL⟩⟩

end HeCent

section Spor1919He

open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He CFSG.Sporadic.HeldB
  CFSG.Sporadic.Schreier

theorem input19_19Spor_he (K : Type) [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hHe : IsSporType .He (K ⧸ Subgroup.center K)) : ¬ IsLocallyOTwoBalancedWrtP 3 1 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hHe
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have β' : CFSG.Blueprint.NativeSporadic.He ≃* (TauCeti.CFSGIndex.sporadic .He).Group := β
  have β'' : CFSG.Blueprint.NativeSporadic.Carrier .He ≃*
      (TauCeti.CFSGIndex.sporadic .He).Group := β
  have hq' : CFSG.IsQuasisimple K :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq⟩
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate K hq'
      ⟨e.trans β'.symm⟩
  let eK : K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (e.trans β''.symm)
  let eP : K ≃* heP := eK.trans heEquivP
  rw [Inputs123a.isLocallyOTwoBalancedWrtP_congr eP]
  have hZP : Subgroup.center heP = ⊥ := by
    rw [← Subgroup.map_center_eq eP, hZ, Subgroup.map_bot]
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥heOuterD) := by rw [card_center_heOuterD]
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hDP : heOuterD ≤ heP := heOuterD_le_C.trans (heOuterC_le_centralizer.trans inf_le_left)
  have hDu : heOuterD ≤ Subgroup.centralizer {heAutU} :=
    heOuterD_le_C.trans (heOuterC_le_centralizer.trans inf_le_right)
  let x : heP := ⟨((z₀ : ↥heOuterD) : Equiv.Perm (Fin 8330)), hDP (z₀ : ↥heOuterD).2⟩
  have hx : orderOf x = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₀]
  have hle : heOuterD ≤ centralizerIn heP (x : Equiv.Perm (Fin 8330)) := by
    intro d hd
    refine mem_centralizerIn.2 ⟨hDP hd, ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z₀.2 ⟨d, hd⟩)
  have hordx : orderOf (x : Equiv.Perm (Fin 8330)) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hcent : centralizerIn heP (x : Equiv.Perm (Fin 8330)) = heOuterD := by
    have hcard : Nat.card (centralizerIn heP (x : Equiv.Perm (Fin 8330))) = 7560 := by
      rcases three_conj_cases x.2 hordx with ⟨c, hc, hcx⟩ | ⟨c, hc, hcx⟩
      · rw [hcx]
        exact (Nat.card_congr (infCentralizerConjEquiv hc (bOf heThreeWordsA)).toEquiv).trans
          card_cent_A
      · exfalso
        have h1 : Nat.card (centralizerIn heP (x : Equiv.Perm (Fin 8330))) = 504 := by
          rw [hcx]
          exact (Nat.card_congr (infCentralizerConjEquiv hc (bOf heThreeWordsB)).toEquiv).trans
            card_cent_B
        have h2 := Subgroup.card_dvd_of_le hle
        rw [card_heOuterD, h1] at h2
        norm_num at h2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_heOuterD])).symm
  let t : MulAut heP := Subgroup.normalizerMonoidHom heP ⟨heAutU, heAutU_mem_normalizer⟩
  have ht : ∀ z : heP, ((t z : heP) : Equiv.Perm (Fin 8330)) = heAutU * z * heAutU⁻¹ :=
    fun z => rfl
  have ht2 : t * t = 1 := by
    rw [← map_mul]
    have h1 : (⟨heAutU, heAutU_mem_normalizer⟩ *
        ⟨heAutU, heAutU_mem_normalizer⟩ : Subgroup.normalizer (heP : Set (Equiv.Perm (Fin 8330)))) =
        1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq]; exact heAutU_sq)
    rw [h1, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    have hall : heP ≤ Subgroup.centralizer {heAutU} := by
      intro z hz
      have h1 : heAutU * z * heAutU⁻¹ = z := by
        have := congrArg (fun φ : MulAut heP => ((φ ⟨z, hz⟩ : heP) : Equiv.Perm (Fin 8330))) h
        exact this
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * heAutU = heAutU * z * heAutU⁻¹ * heAutU := by rw [h1]
        _ = heAutU * z := by group
    have h1 : heP ⊓ Subgroup.centralizer {heAutU} = heP := inf_eq_left.2 hall
    have h2 := card_heP_centralizer_heAutU
    rw [h1, card_heP] at h2
    norm_num at h2
  have htx : t x = x := by
    apply Subtype.ext
    rw [ht]
    have hxu := Subgroup.mem_centralizer_singleton_iff.1 (hDu (z₀ : ↥heOuterD).2)
    calc heAutU * (x : Equiv.Perm (Fin 8330)) * heAutU⁻¹ = x * heAutU * heAutU⁻¹ := by
          rw [← hxu]
      _ = x := by group
  have hC : ∀ z : heP, z * x = x * z → t z = z := by
    intro z hz
    have hzc : (z : Equiv.Perm (Fin 8330)) ∈ centralizerIn heP (x : Equiv.Perm (Fin 8330)) :=
      mem_centralizerIn.2 ⟨z.2, congrArg Subtype.val hz⟩
    rw [hcent] at hzc
    have hzu := Subgroup.mem_centralizer_singleton_iff.1 (hDu hzc)
    apply Subtype.ext
    rw [ht]
    calc heAutU * (z : Equiv.Perm (Fin 8330)) * heAutU⁻¹ = z * heAutU * heAutU⁻¹ := by
          rw [← hzu]
      _ = z := by group
  exact Input1919.not_balanced_of_inv Nat.prime_three hZP hx ht2 ht1 htx hC

end Spor1919He

section Spor1919Fi22

open CFSG.RankThree.Native CFSG.Monster.B.Fischer

theorem input19_19Spor_fi22 (K : Type) [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hFi : IsSporType .Fi22 (K ⧸ Subgroup.center K)) : ¬ IsLocallyOTwoBalancedWrtP 5 1 K := by
  obtain ⟨e⟩ := hFi
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have β' : CFSG.Blueprint.NativeSporadic.Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := β
  have β'' : CFSG.Blueprint.NativeSporadic.Carrier .Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group := β
  have hK : commutator K = ⊤ := hq.1
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (K ⧸ Subgroup.center K)) = 6 := by
    rw [CFSG.Quasithin.H13.L3317.card_hopfMultiplier_congr (e.trans β''.symm)]
    exact CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_of_two_one_three_one rfl
      (CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_of_ne_M _ (by decide))
      CFSG.EvenSporadicStandard.rowBound_Fi22
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.two_dvd_card_hopfMultiplier_Fi22
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeCell3_Fi22
      (CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.bigPrimeFacts_of_ne_M .Fi22 (by decide))
  have hs := Input1919.autQ_surjective hK
    (Input1919.gcd_dvd_of_two_or_six (Or.inr hM) (Input1919.card_center_dvd_hopf hK))
  refine Input1919.not_balanced_of_autQ_surjective hK hs ?_
  let θ : (K ⧸ Subgroup.center K) ≃* fi22P := (e.trans β'.symm).trans fi22PermEquiv
  rw [Inputs123a.isLocallyOTwoBalancedWrtP_congr θ]
  have hZP : Subgroup.center fi22P = ⊥ :=
    CFSG.HardMathSupport.Solomon.Proving.fi22_centre_eq_bot fi22PermEquiv.symm
  let x : fi22P := ⟨fi22FiveLine 0, fi22FiveLine_mem_P 0⟩
  have hx : orderOf x = 5 := by rw [Subgroup.orderOf_mk, orderOf_fi22FiveLine]
  let t : MulAut fi22P := fi22ConjHom ⟨fi22FiveW, fi22FiveW_mem_R⟩
  have ht : ∀ z : fi22P, ((t z : fi22P) : Equiv.Perm (Fin 3510)) = fi22FiveW * z * fi22FiveW⁻¹ :=
    fun z => fi22ConjHom_apply _ _
  have ht2 : t * t = 1 := by
    rw [← map_mul]
    have h1 : (⟨fi22FiveW, fi22FiveW_mem_R⟩ * ⟨fi22FiveW, fi22FiveW_mem_R⟩ : fi22R) = 1 :=
      Subtype.ext fi22FiveW_mul_self
    rw [h1, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h1 := fi22ConjHom_injective (h.trans (map_one fi22ConjHom).symm)
    exact fi22FiveW_ne_one (congrArg Subtype.val h1)
  have htx : t x = x := by
    apply Subtype.ext
    rw [ht]
    calc fi22FiveW * (x : Equiv.Perm (Fin 3510)) * fi22FiveW⁻¹ =
        x * fi22FiveW * fi22FiveW⁻¹ := by rw [fi22FiveW_comm_line 0]
      _ = x := by group
  have hC : ∀ z : fi22P, z * x = x * z → t z = z := by
    intro z hz
    have hzC : (z : Equiv.Perm (Fin 3510)) ∈ fi22FiveC 0 := by
      have h1 : (z : Equiv.Perm (Fin 3510)) ∈ Subgroup.centralizer {fi22FiveLine 0} ⊓ fi22P :=
        Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hz), z.2⟩
      rw [← fi22FiveC_inf_P 0] at h1
      exact (Subgroup.mem_inf.1 h1).1
    have hzw := Subgroup.mem_centralizer_singleton_iff.1 (fi22FiveC_le_centralizer_W 0 hzC)
    apply Subtype.ext
    rw [ht]
    calc fi22FiveW * (z : Equiv.Perm (Fin 3510)) * fi22FiveW⁻¹ = z * fi22FiveW * fi22FiveW⁻¹ := by
          rw [← hzw]
      _ = z := by group
  exact Input1919.not_balanced_of_inv (by norm_num) hZP hx ht2 ht1 htx hC

end Spor1919Fi22

section Spor1919

theorem input19_19Spor_holds : Input1919.Input19_19Spor := fun K _ _ hq =>
  ⟨input19_19Spor_fi22 K hq, input19_19Spor_he K hq⟩

end Spor1919

section HeGen

open CFSG.GH74.KGroups CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
  CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem inputHeGen_holds : Prop126b.InputHeGen := by
  intro Y _ _ K B hq hHe hBN hBe hrk hnt
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHe' := hHe
  obtain ⟨e⟩ := hHe
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have β' : CFSG.Blueprint.NativeSporadic.He ≃* (TauCeti.CFSGIndex.sporadic .He).Group := β
  have β'' : CFSG.Blueprint.NativeSporadic.Carrier .He ≃*
      (TauCeti.CFSGIndex.sporadic .He).Group := β
  let f₀ : (↥K ⧸ Subgroup.center ↥K) ≃* CFSG.Blueprint.NativeSporadic.He := e.trans β'.symm
  have hq' : CFSG.IsQuasisimple ↥K :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq⟩
  have hZ : Subgroup.center ↥K = ⊥ :=
    CFSG.Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate ↥K hq' ⟨f₀⟩
  let eQ : ↥K ≃* (↥K ⧸ Subgroup.center ↥K) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let eK : ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He := eQ.trans (e.trans β''.symm)
  let eP : ↥K ≃* heP := eK.trans heEquivP
  have hout : Nat.card (Outer ↥K) ≤ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eK).toEquiv]
    exact CFSG.Sporadic.Schreier.AT_He_Schreier.1
  have hcop : Nat.Coprime 3 (Nat.card (Outer ↥K)) :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.coprime_of_le_two Nat.prime_three (by norm_num)
      Nat.card_pos.ne' hout
  have hconjinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) :=
    Input1919.conj_injective_of_center hZ
  have step : ∀ (b : Y) (k : ↥K), (∀ q : ↥K, ((k * q * k⁻¹ : ↥K) : Y) = b * q * b⁻¹) → k ≠ 1 →
      k ^ 3 = 1 → ∀ τ ∈ K ⊓ Subgroup.centralizer ({b} : Set Y), Nat.Coprime (orderOf τ) 3 →
        τ ∈ GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) := by
    intro b k hkb hk1 hk3 τ hτ hτ3
    have hordk : orderOf k = 3 := orderOf_eq_prime hk3 hk1
    have hcent : ∀ q : ↥K, (q : Y) ∈ Subgroup.centralizer ({b} : Set Y) ↔ q * k = k * q := by
      intro q
      rw [Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h1 : ((k * q * k⁻¹ : ↥K) : Y) = q := by
          rw [hkb]
          calc b * (q : Y) * b⁻¹ = q * b * b⁻¹ := by rw [h]
            _ = q := by group
        have h2 : k * q * k⁻¹ = q := Subtype.ext h1
        calc q * k = k * q * k⁻¹ * k := by rw [h2]
          _ = k * q := by group
      · intro h
        have h1 : k * q * k⁻¹ = q := by rw [← h]; group
        have h2 : b * (q : Y) * b⁻¹ = q := by rw [← hkb, h1]
        calc (q : Y) * b = b * q * b⁻¹ * b := by rw [h2]
          _ = b * q := by group
    have hordP : orderOf ((eP k : heP) : Equiv.Perm (Fin 8330)) = 3 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hordk]
    have transport : ∀ (ws : List (List ℤ)) (c : Equiv.Perm (Fin 8330)) (hc : c ∈ heP),
        ((eP k : heP) : Equiv.Perm (Fin 8330)) = c * bOf ws * c⁻¹ →
        ∀ D : Subgroup (Equiv.Perm (Fin 8330)), GLAPComponent 3 (centralizerIn heP (bOf ws)) D →
          (∀ x ∈ centralizerIn heP (bOf ws), Nat.Coprime (orderOf x) 3 → x ∈ D) →
          τ ∈ GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) := by
      intro ws c hc hcx D hD hD3
      let φ : ↥K ≃* heP := eP.trans (MulAut.conj (⟨c, hc⟩ : heP)⁻¹)
      have hφ : ((φ k : heP) : Equiv.Perm (Fin 8330)) = bOf ws := by
        show c⁻¹ * ((eP k : heP) : Equiv.Perm (Fin 8330)) * c = bOf ws
        rw [hcx]
        group
      let ψ : ↥heP →* Y := K.subtype.comp φ.symm.toMonoidHom
      have hψinj : Function.Injective ψ := Subtype.val_injective.comp φ.symm.injective
      have hCle : centralizerIn heP (bOf ws) ≤ heP := inf_le_left
      have hCmap : ((centralizerIn heP (bOf ws)).subgroupOf heP).map ψ =
          K ⊓ Subgroup.centralizer ({b} : Set Y) := by
        ext y
        constructor
        · intro hy
          obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
          rw [Subgroup.mem_subgroupOf] at hx
          obtain ⟨-, hxc⟩ := mem_centralizerIn.1 hx
          refine Subgroup.mem_inf.2 ⟨(φ.symm x).2, (hcent _).2 ?_⟩
          apply φ.injective
          apply Subtype.ext
          rw [map_mul, map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
            Subgroup.coe_mul, Subgroup.coe_mul, hφ]
          exact hxc
        · intro hy
          obtain ⟨hyK, hyb⟩ := Subgroup.mem_inf.1 hy
          have hyc := (hcent ⟨y, hyK⟩).1 hyb
          refine Subgroup.mem_map.2 ⟨φ ⟨y, hyK⟩, ?_, ?_⟩
          · rw [Subgroup.mem_subgroupOf]
            refine mem_centralizerIn.2 ⟨(φ ⟨y, hyK⟩).2, ?_⟩
            rw [← hφ]
            have := congrArg (fun z => ((φ z : heP) : Equiv.Perm (Fin 8330))) hyc
            simpa only [map_mul, Subgroup.coe_mul] using this
          · show ((φ.symm (φ ⟨y, hyK⟩) : ↥K) : Y) = y
            rw [MulEquiv.symm_apply_apply]
      have hDcomp : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))
          ((D.subgroupOf heP).map ψ) := by
        rw [← hCmap]
        refine glaPComponent_map Nat.prime_three ψ ?_
          (Prop126b.glaPComponent_subgroupOf Nat.prime_three hCle hD)
        rw [(MonoidHom.ker_eq_bot_iff ψ).2 hψinj, inf_bot_eq, Subgroup.card_bot]
        exact Nat.coprime_one_right 3
      have hτmem : τ ∈ (D.subgroupOf heP).map ψ := by
        rw [← hCmap] at hτ
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hτ
        refine Subgroup.mem_map.2 ⟨x, ?_, rfl⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        refine hD3 _ hx ?_
        rw [Subgroup.orderOf_coe, ← orderOf_injective ψ hψinj x]
        exact hτ3
      have hle : (D.subgroupOf heP).map ψ ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) := by
        unfold GLAPLayer
        exact le_sSup hDcomp
      exact hle hτmem
    rcases three_conj_cases (eP k).2 hordP with ⟨c, hc, hcx⟩ | ⟨c, hc, hcx⟩
    · refine transport heThreeWordsA c hc hcx heTcQ heThreeA_component fun x hx _ => ?_
      rw [← heTcQ_eq] at hx
      exact hx
    · obtain ⟨D, -, -, hDcomp, hD3⟩ := heThreeB_component
      exact transport heThreeWordsB c hc hcx D hDcomp hD3
  let ρ : ↥B →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hBN)
  have hρ : ∀ (b : ↥B) (q : ↥K), ((ρ b q : ↥K) : Y) = b * q * b⁻¹ := fun b q => rfl
  have hB3 : ∀ b : ↥B, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBe.2 b b.2)
  have hρ1 : ∀ b : ↥B, ρ b = 1 → b = 1 := by
    intro b hb
    by_contra hb1
    have hb1' : (b : Y) ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨q, hqK, hbq⟩ := hnt b b.2 hb1'
    apply hbq
    have h1 : (b : Y) * q * (b : Y)⁻¹ = q := by
      have := congrArg (fun φ : MulAut ↥K => ((φ ⟨q, hqK⟩ : ↥K) : Y)) hb
      exact this
    calc (b : Y) * q = (b : Y) * q * (b : Y)⁻¹ * b := by group
      _ = q * b := by rw [h1]
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    exact (Subgroup.mem_bot).2 (hρ1 b (MonoidHom.mem_ker.1 hb))
  have hRp : IsPGroup 3 ↥ρ.range := by
    rintro ⟨φ, b, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hB3 b, map_one]
  have hin : ρ.range ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.le_inner_of_isPGroup hcop hRp
  set E : Subgroup ↥K := ρ.range.comap MulAut.conj with hE
  have hEmap : E.map MulAut.conj = ρ.range := by
    rw [hE, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hin
  have hcardE : Nat.card E = Nat.card B := by
    rw [← Subgroup.card_map_of_injective hconjinj, hEmap]
    exact (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  have hBp : IsPGroup 3 B := fun b => ⟨1, by rw [pow_one]; exact hB3 b⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 hBp
  have hr2 : 2 ≤ r := by
    have h1 : CFSG.Open.pRank 3 B ≤ r := pRank_le_of_forall fun E' hE'B _ k hk => by
      have h := Subgroup.card_le_of_le hE'B
      rw [hk, hr] at h
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
    omega
  have hr2' : r ≤ 2 := by
    have hRe : CFSG.Open.IsElemAbelian 3 ρ.range := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨_, x, rfl⟩ := a
        obtain ⟨_, y, rfl⟩ := b
        apply Subtype.ext
        show ρ x * ρ y = ρ y * ρ x
        rw [← map_mul, ← map_mul]
        congr 1
        exact hBe.1.is_comm.comm x y
      · rintro _ ⟨b, rfl⟩
        rw [← map_pow, hB3 b, map_one]
    have hrank := pRank_aut_He hq e
    have hcardR : Nat.card ρ.range = 3 ^ r := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv, hr]
    haveI : Finite (MulAut ↥K) := inferInstance
    have hmem : r ∈ {k | ∃ E' : Subgroup (MulAut ↥K), E' ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E' ∧
        Nat.card E' = 3 ^ k} := ⟨ρ.range, le_top, hRe, hcardR⟩
    have hbdd : BddAbove {k | ∃ E' : Subgroup (MulAut ↥K), E' ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E' ∧
        Nat.card E' = 3 ^ k} := by
      refine ⟨Nat.card (MulAut ↥K), fun k ⟨E', _, _, hk⟩ => ?_⟩
      have h1 : 3 ^ k ≤ Nat.card (MulAut ↥K) := hk ▸ Subgroup.card_le_card_group E'
      exact (Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans h1
    have := le_csSup hbdd hmem
    unfold CFSG.Open.pRank at hrank
    omega
  have hB9 : Nat.card B = 9 := by
    rw [hr, show r = 2 by omega]
    norm_num
  set P' : Subgroup heP := E.map eP.toMonoidHom with hP'
  have hP'9 : Nat.card P' = 9 := by
    rw [hP', Subgroup.card_map_of_injective eP.injective, hcardE, hB9]
  have hFG : CFSG.RankThree.PartTwo.Sec4.Item434SporGen.FixGen P' :=
    CFSG.RankThree.PartTwo.Sec4.Item434SporGen.fixGen_of_ex27Check (rep_heGen (k := 0) (by norm_num))
      (rep_heGen (k := 1) (by norm_num)) CFSG.RankThree.PartTwo.Sec4.Item434SporGen.heP_eq_closure_gens
      CFSG.RankThree.PartTwo.Sec4.Item434SporGen.factorization_card_heP
      CFSG.RankThree.PartTwo.Sec4.Item434SporGen.he_check P' hP'9
  obtain ⟨S', hS'top, hS'⟩ := hFG
  have hSmem : ∀ σ' ∈ S', ((eP.symm σ' : ↥K) : Y) ∈
      ⨆ (b : Y) (_ : b ∈ B) (_ : b ≠ 1), GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) := by
    intro σ' hσ'
    obtain ⟨hcop3, p, hpP, hp1, hpσ⟩ := hS' σ' hσ'
    obtain ⟨k, hkE, rfl⟩ := Subgroup.mem_map.1 hpP
    obtain ⟨b, hb⟩ := (Subgroup.mem_comap.1 hkE : MulAut.conj k ∈ ρ.range)
    have hk1 : k ≠ 1 := fun h => hp1 (by rw [h, map_one])
    have hb1 : (b : Y) ≠ 1 := by
      intro h
      apply hk1
      apply hconjinj
      rw [← hb, map_one]
      have : b = 1 := Subtype.ext h
      rw [this, map_one]
    have hkb : ∀ q : ↥K, ((k * q * k⁻¹ : ↥K) : Y) = (b : Y) * q * (b : Y)⁻¹ := by
      intro q
      rw [← Subgroup.coe_inv, ← hρ, hb]
      rfl
    have hk3 : k ^ 3 = 1 := by
      apply hconjinj
      rw [map_pow, ← hb, ← map_pow, hB3 b, map_one, map_one]
    have hσK : ((eP.symm σ' : ↥K) : Y) ∈ K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y) := by
      refine Subgroup.mem_inf.2 ⟨(eP.symm σ').2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : k * eP.symm σ' = eP.symm σ' * k := by
        apply eP.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hpσ
      have h2 : ((k * eP.symm σ' * k⁻¹ : ↥K) : Y) = eP.symm σ' := by
        rw [h1, mul_inv_cancel_right]
      rw [hkb] at h2
      calc ((eP.symm σ' : ↥K) : Y) * b = (b : Y) * (eP.symm σ' : ↥K) * (b : Y)⁻¹ * b := by
            rw [h2]
        _ = b * (eP.symm σ' : ↥K) := by group
    have hord : Nat.Coprime (orderOf ((eP.symm σ' : ↥K) : Y)) 3 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hcop3
    have hL := step b k hkb hk1 hk3 _ hσK hord
    exact (le_iSup₂ (f := fun (b' : Y) (_ : b' ∈ B) =>
      ⨆ (_ : b' ≠ 1), GLAPLayer 3 (K ⊓ Subgroup.centralizer ({b'} : Set Y))) (b : Y) b.2)
      ((le_iSup (fun _ : (b : Y) ≠ 1 =>
        GLAPLayer 3 (K ⊓ Subgroup.centralizer ({(b : Y)} : Set Y))) hb1) hL)
  intro y hy
  have h1 : (⟨y, hy⟩ : ↥K) ∈ Subgroup.closure (eP.symm '' S') := by
    have h2 : (⊤ : Subgroup ↥K) ≤ Subgroup.closure (eP.symm '' S') := by
      have h3 : (Subgroup.closure S').map eP.symm.toMonoidHom = ⊤ := by
        rw [eq_top_iff.2 hS'top, Subgroup.map_top_of_surjective _ eP.symm.surjective]
      rw [← h3, MonoidHom.map_closure]
      rfl
    exact h2 (Subgroup.mem_top _)
  have h4 : y ∈ (Subgroup.closure (eP.symm '' S')).map K.subtype := ⟨⟨y, hy⟩, h1, rfl⟩
  rw [MonoidHom.map_closure] at h4
  refine (Subgroup.closure_le _).2 ?_ h4
  rintro _ ⟨_, ⟨σ', hσ', rfl⟩, rfl⟩
  exact hSmem σ' hσ'

end HeGen

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporFacts
