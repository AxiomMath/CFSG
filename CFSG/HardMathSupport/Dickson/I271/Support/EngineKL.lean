module

public import CFSG.HardMathSupport.Dickson.I271.Support.EngineTB
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Aut
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Red
public import CFSG.LocalAnalysis.GLTheoremB.Input20_1Proof

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Balance

open scoped commutatorElement

theorem glaPComponent_of_normal {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X K : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥K) (hpK : p ∣ Nat.card K) (hKX : K ≤ X)
    (hKn : (K.subgroupOf X).Normal) : GLAPComponent p X K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsn : IsSubnormal K X := isSubnormal_of_normal hKX hKn
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hπ
  set ψ : ↥K →* ↥X ⧸ GLAPPrimeCore p ↥X := π.comp (Subgroup.inclusion hKX) with hψ
  have hrange : ψ.range = (K.subgroupOf X).map π := by
    ext z
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKX k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hker : ψ.ker ≠ ⊤ := by
    intro htop
    have hle : K.subgroupOf X ≤ GLAPPrimeCore p ↥X := by
      intro y hy
      have : (⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩ : ↥K) ∈ ψ.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker] at this
      exact (QuotientGroup.eq_one_iff y).1 this
    have h1 : Nat.card (K.subgroupOf X) ∣ Nat.card (GLAPPrimeCore p ↥X) :=
      Subgroup.card_dvd_of_le hle
    have h2 : Nat.card (K.subgroupOf X) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
    have h3 : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥X)) := CFSG.pPrimeCore_coprime_card
    rw [h2] at h1
    exact hp.one_lt.ne' (h3.eq_one_of_dvd (hpK.trans h1))
  have hqK : CFSG.Open.IsQuasisimple ↥((K.subgroupOf X).map π) := by
    rw [← hrange]
    exact CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hq ψ hker
  have hnorm : ((K.subgroupOf X).map π).Normal :=
    Subgroup.Normal.map hKn π (QuotientGroup.mk'_surjective _)
  refine ⟨hKX, hsn, ⟨le_top, isSubnormal_of_normal le_top inferInstance, hqK⟩, ?_⟩
  intro J hlt hJsn heq
  have hJK : IsSubnormal J K := isSubnormal_of_le_of_le hJsn hlt.le hKX
  have hJK' : IsSubnormal (J.subgroupOf K) ⊤ := by
    have h1 := isSubnormal_comap' K.subtype hJK
    rwa [show K.comap K.subtype = ⊤ from Subgroup.subgroupOf_self K] at h1
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hq
    (J.subgroupOf K) hJK' with hc | htop
  ·
    have hcomm : ∀ a ∈ (K.subgroupOf X).map π, ∀ b ∈ (K.subgroupOf X).map π, a * b = b * a := by
      intro a ha b hb
      rw [← heq] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨z, hz, rfl⟩ := hb
      have hyJ : (y : G) ∈ J := Subgroup.mem_subgroupOf.1 hy
      have hzK : (z : G) ∈ K := Subgroup.mem_subgroupOf.1 hz
      have hcen := Subgroup.mem_center_iff.1
        (hc (show (⟨(y : G), hlt.le hyJ⟩ : ↥K) ∈ J.subgroupOf K from hyJ)) ⟨(z : G), hzK⟩
      have : y * z = z * y := Subtype.ext (congrArg Subtype.val hcen).symm
      rw [← map_mul, ← map_mul, this]
    have hcomm' : ∀ a b : ↥((K.subgroupOf X).map π), a * b = b * a := fun a b =>
      Subtype.ext (hcomm a a.2 b b.2)
    haveI : Group.IsSolvable ↥((K.subgroupOf X).map π) := isSolvable_of_comm hcomm'
    haveI : Group.IsPerfect ↥((K.subgroupOf X).map π) := ⟨hqK.1⟩
    haveI := CFSG.ComponentClassification.Quasisimple.nontrivial hqK
    exact Group.IsPerfect.not_isSolvable _
      (inferInstance : Group.IsSolvable ↥((K.subgroupOf X).map π))
  · exact hlt.ne' (le_antisymm (Subgroup.subgroupOf_eq_top.1 htop) hlt.le)

theorem isCompLocallyBalanced_mono {G : Type*} [Group G] {p k : ℕ} {A D L : Subgroup G}
    (h : IsCompLocallyBalanced p k A L) (hDA : D ≤ A) : IsCompLocallyBalanced p k D L := by
  intro E hE H hH hEH
  have hmono : autBar p D L ≤ autBar p A L :=
    Subgroup.map_mono fun x hx =>
      (Subgroup.mem_subgroupOf).2 (inf_le_inf_right _ hDA ((Subgroup.mem_subgroupOf).1 hx))
  exact h E ⟨hE.1.trans hmono, hE.2⟩ H hH hEH

theorem core_le_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X₁ K A : Subgroup G} {a : G} (hq : CFSG.Open.IsQuasisimple ↥K) (hpK : p ∣ Nat.card K)
    (hKX : K ≤ X₁) (hKn : (K.subgroupOf X₁).Normal) (haX : a ∈ X₁) (haA : a ∈ A) (ha1 : a ≠ 1)
    (hap : a ^ p = 1) (hloc : IsCompLocallyBalanced p 1 A K) :
    GLAPPrimeCoreOf p (X₁ ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      Subgroup.centralizer (K : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hKc : GLAPComponent p X₁ K := glaPComponent_of_normal hp hq hpK hKX hKn
  have hX₁N : X₁ ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).1 hKn
  set C := X₁ ⊓ Subgroup.centralizer ({a} : Set G) with hC
  set S := GLAPPrimeCoreOf p C with hS
  set D := Subgroup.zpowers a with hD
  have haC : a ∈ C := ⟨haX, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hSC : S ≤ C := Subgroup.map_subtype_le _
  have hDel : IsElemAbelian p D := by
    rw [hD, Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro x hx y hy
      rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]
    · intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact hap
  have hDcard : Nat.card D = p ^ 1 := by
    rw [hD, Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hap ha1
  have hcentEq : ∀ e ∈ D, e ≠ 1 → Subgroup.centralizer ({e} : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
    intro e he he1
    have hep : e ^ p = 1 := hDel.2 e he
    have hzz : Subgroup.zpowers e = Subgroup.zpowers a := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 he) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hap ha1, orderOf_eq_prime hep he1]
    have e1 : ∀ g : G, Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) =
        Subgroup.centralizer ({g} : Set G) := fun g => by
      rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_closure _
    rw [← e1 e, ← e1 a, hzz]
  have hID : InDelta p X₁ D S := by
    refine ⟨Subgroup.zpowers_le.2 haX, hDel, ?_, hSC.trans inf_le_left, ?_⟩
    · intro h
      exact ha1 (by simpa [hD] using h)
    · intro e he he1
      rw [hcentEq e he he1]
  have hDS : D ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.zpowers_le.2 (le_normalizer_glaPPrimeCoreOf p C haC)
  have hcomm : ⁅K, S⁆ ≤ GLAPPrimeCoreOf p X₁ := by
    by_contra hn
    exact (hID.conclusions h1Stmt_holds hp hKc hDcard hDS hn).2.2.2.2
      (isCompLocallyBalanced_mono hloc (Subgroup.zpowers_le.2 haA))
  have hKS : ⁅K, S⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk s hs
    have hsN := hX₁N (hSC.trans inf_le_left hs)
    have h1 := (Subgroup.mem_normalizer_iff.1 hsN (k⁻¹)).1 (K.inv_mem hk)
    have : ⁅k, s⁆ = k * (s * k⁻¹ * s⁻¹) := by group
    rw [this]
    exact K.mul_mem hk h1
  have hTcen : K ⊓ GLAPPrimeCoreOf p X₁ ≤ Subgroup.centralizer (K : Set G) := by
    have hnormO : X₁ ≤ Subgroup.normalizer (GLAPPrimeCoreOf p X₁ : Set G) :=
      le_normalizer_glaPPrimeCoreOf p X₁
    have hTn : ((K ⊓ GLAPPrimeCoreOf p X₁).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun x hx =>
        mem_normalizer_inf (hX₁N (hKX hx)) (hnormO (hKX hx))
    haveI := hTn
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      ((K ⊓ GLAPPrimeCoreOf p X₁).subgroupOf K) with hc | htop
    · intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := Subgroup.mem_center_iff.1
        (hc (show (⟨t, ht.1⟩ : ↥K) ∈ (K ⊓ GLAPPrimeCoreOf p X₁).subgroupOf K from ht))
        ⟨k, hk⟩
      exact congrArg Subtype.val this
    · exfalso
      have hKO : K ≤ GLAPPrimeCoreOf p X₁ := fun x hx =>
        ((Subgroup.subgroupOf_eq_top.1 htop) hx).2
      have h1 : Nat.card K ∣ Nat.card (GLAPPrimeCoreOf p X₁) := Subgroup.card_dvd_of_le hKO
      exact not_dvd_card_glaPPrimeCoreOf hp X₁ (hpK.trans h1)
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hdbl : ⁅⁅K, S⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun x hx => hTcen ⟨hKS hx, hcomm hx⟩
  have hKS0 : ⁅K, S⁆ = ⊥ := CFSG.ComponentClassification.Quasisimple.perfect_double_commutator K S hdbl
  rw [Subgroup.commutator_comm] at hKS0
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKS0 |>.trans le_rfl

@[expose] noncomputable def bar0 {G : Type*} [Group G] (p : ℕ) {C N : Subgroup G} (hNC : N ≤ C) :
    ↥N →* ↥C ⧸ GLAPPrimeCore p ↥C :=
  (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Subgroup.inclusion hNC)

theorem bar0_range {G : Type*} [Group G] (p : ℕ) {C N : Subgroup G} (hNC : N ≤ C) :
    (bar0 p hNC).range = barX p C N := by
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Subgroup.inclusion hNC k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩

theorem bar0_ker {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {C N : Subgroup G}
    (hN : IsSubnormal N C) : (bar0 p hN.le).ker = GLAPPrimeCore p ↥N := by
  ext x
  rw [MonoidHom.mem_ker]
  have h1 : bar0 p hN.le x = 1 ↔ (⟨(x : G), hN.le x.2⟩ : ↥C) ∈ GLAPPrimeCore p ↥C :=
    QuotientGroup.eq_one_iff _
  rw [h1]
  have h2 : (⟨(x : G), hN.le x.2⟩ : ↥C) ∈ GLAPPrimeCore p ↥C ↔
      (x : G) ∈ GLAPPrimeCoreOf p C := by
    rw [mem_gLAPPrimeCoreOf_iff]
    exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
  rw [h2]
  have h3 : (x : G) ∈ GLAPPrimeCoreOf p C ↔ (x : G) ∈ GLAPPrimeCoreOf p N := by
    rw [← inf_gLAPPrimeCoreOf_eq hp hN]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [h3, mem_gLAPPrimeCoreOf_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

@[expose] noncomputable def bar0Equiv {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C N : Subgroup G} (hN : IsSubnormal N C) : barOf p N ≃* ↥(bar0 p hN.le).range :=
  (QuotientGroup.quotientMulEquivOfEq (bar0_ker hp hN)).symm.trans
    (QuotientGroup.quotientKerEquivRange (bar0 p hN.le))

theorem bar0Equiv_mk {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {C N : Subgroup G}
    (hN : IsSubnormal N C) (x : ↥N) :
    ((bar0Equiv hp hN (QuotientGroup.mk x) : ↥(bar0 p hN.le).range) :
      ↥C ⧸ GLAPPrimeCore p ↥C) = bar0 p hN.le x := rfl

theorem barX_le_centralizer_components {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C N M W₁ : Subgroup G} (hNC : N ≤ C) (hNn : (N.subgroupOf C).Normal) (hNM : N ≤ M)
    (hexp : ∀ x ∈ M, ∃ n : ℕ, Nat.Coprime p n ∧ x ^ n ∈ N)
    (hab : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ M)
    (hJ : ∀ J, GLAPComponent p N J → ∀ w ∈ W₁, ∀ j ∈ J, w ∈ C →
      w * j * w⁻¹ * j⁻¹ ∈ GLAPPrimeCoreOf p C)
    (L : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) (hL : IsComponentOf L ⊤) :
    barX p C W₁ ≤ Subgroup.centralizer (L : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  have hO : GLAPPrimeCore p (↥C ⧸ GLAPPrimeCore p ↥C) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  haveI : (barX p C N).Normal := Subgroup.Normal.map hNn π (QuotientGroup.mk'_surjective _)
  have hexpZ : ∀ x ∈ barX p C M, ∃ n : ℕ, Nat.Coprime p n ∧ x ^ n ∈ barX p C N := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨n, hn, hyn⟩ := hexp (y : G) (Subgroup.mem_subgroupOf.1 hy)
    refine ⟨n, hn, ⟨y ^ n, Subgroup.mem_subgroupOf.2 (by simpa using hyn), by rw [map_pow]⟩⟩
  have habZ : commutator (↥C ⧸ GLAPPrimeCore p ↥C) ≤ barX p C M := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro z₁ _ z₂ _
    obtain ⟨y₁, rfl⟩ := QuotientGroup.mk_surjective z₁
    obtain ⟨y₂, rfl⟩ := QuotientGroup.mk_surjective z₂
    refine ⟨⁅y₁, y₂⁆, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · exact hab y₁ y₁.2 y₂ y₂.2
    · rw [map_commutatorElement]
      rfl
  have hMsub : barX p C N ≤ barX p C M :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2
      (hNM (Subgroup.mem_subgroupOf.1 hx))
  have hle : L ≤ barX p C N :=
    le_of_isComponentOf_of_coprime_quotient hp hO hMsub hexpZ habZ hL
  have hNsub : IsSubnormal N C := isSubnormal_of_normal hNC hNn
  have hrange : (bar0 p hNsub.le).range = barX p C N := bar0_range p hNsub.le
  have hle' : L ≤ (bar0 p hNsub.le).range := hrange ▸ hle
  set e := bar0Equiv hp hNsub with he
  have hL' : IsComponentOf (L.subgroupOf (bar0 p hNsub.le).range) ⊤ :=
    CFSG.ComponentClassification.LocalComponents.of_overgroup hL hle'
  have hL'' : IsComponentOf ((L.subgroupOf (bar0 p hNsub.le).range).map e.symm.toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff e.symm _).2 hL'
  obtain ⟨J, hJc, hbar⟩ := exists_glaPComponent_barX_eq N hL''
  have hJN : J ≤ N := hJc.1
  have hLJ : L = barX p C J := by
    apply le_antisymm
    · intro z hz
      have hζ : (⟨z, hle' hz⟩ : ↥(bar0 p hNsub.le).range) ∈
          L.subgroupOf (bar0 p hNsub.le).range := hz
      have hmem : e.symm ⟨z, hle' hz⟩ ∈ barX p N J := by
        rw [hbar]
        exact ⟨_, hζ, rfl⟩
      obtain ⟨j, hj, hjeq⟩ := hmem
      have h1 : e (QuotientGroup.mk j) = ⟨z, hle' hz⟩ := by
        have : QuotientGroup.mk' (GLAPPrimeCore p ↥N) j = e.symm ⟨z, hle' hz⟩ := hjeq
        rw [QuotientGroup.mk'_apply] at this
        rw [this, MulEquiv.apply_symm_apply]
      have h2 := congrArg Subtype.val h1
      rw [bar0Equiv_mk hp hNsub] at h2
      exact ⟨⟨(j : G), hNC j.2⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hj), h2⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyJ : (y : G) ∈ J := Subgroup.mem_subgroupOf.1 hy
      have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (⟨(y : G), hJN hyJ⟩ : ↥N) ∈ barX p N J :=
        ⟨_, Subgroup.mem_subgroupOf.2 hyJ, rfl⟩
      rw [hbar] at hmem
      obtain ⟨ℓ, hℓ, hℓeq⟩ := hmem
      have h1 : e (QuotientGroup.mk (⟨(y : G), hJN hyJ⟩ : ↥N)) = ℓ := by
        have : e.symm.toMonoidHom ℓ = QuotientGroup.mk (⟨(y : G), hJN hyJ⟩ : ↥N) := hℓeq
        rw [← this]
        exact e.apply_symm_apply ℓ
      have h2 := congrArg Subtype.val h1
      rw [bar0Equiv_mk hp hNsub] at h2
      have : π y = (ℓ : ↥C ⧸ GLAPPrimeCore p ↥C) := h2
      rw [this]
      exact hℓ
  rw [hLJ]
  exact barX_le_centralizer fun s hs t ht hsC htC => hJ J hJc s hs t ht hsC

theorem isSCp_subgroupOf_of_le {G : Type*} [Group G] {p : ℕ} {X₁ C B : Subgroup G}
    (hB : IsSCp p X₁ B) (hBC : B ≤ C) (hCX : C ≤ X₁) : IsSCp p ⊤ (B.subgroupOf C) := by
  obtain ⟨-, hel, hmax⟩ := hB
  have := hel.1
  refine ⟨le_top, ⟨inferInstance, fun x hx => Subtype.ext (hel.2 x hx)⟩, ?_⟩
  intro E _ hE hBE
  have hE' : IsElemAbelian p (E.map C.subtype) := CFSG.SectionRank.isElemAbelian_map hE _
  have hBE' : B ≤ E.map C.subtype := fun x hx => ⟨⟨x, hBC hx⟩, hBE hx, rfl⟩
  have hEC : E.map C.subtype ≤ X₁ := (Subgroup.map_subtype_le E).trans hCX
  have h := hmax _ hEC hE' hBE'
  calc E = (E.map C.subtype).comap C.subtype :=
        (Subgroup.comap_map_eq_self_of_injective C.subtype_injective E).symm
    _ = B.subgroupOf C := by rw [h]; rfl

theorem local_step {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K B A X₁ W : Subgroup X} {a : X} (hq : CFSG.Open.IsQuasisimple ↥K) (hpK : p ∣ Nat.card K)
    (hKX : K ≤ X₁) (hKn : (K.subgroupOf X₁).Normal) (hBX : B ≤ X₁) (hWX : W ≤ X₁)
    (hBel : IsElemAbelian p B) (hSC : IsSCp p X₁ B) (hAB : A ≤ B) (haA : a ∈ A) (ha1 : a ≠ 1)
    (hloc : IsCompLocallyBalanced p 1 A K)
    (hcomp : ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
      B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced p B a J)
    (hWK : W ≤ Subgroup.normalizer (K : Set X)) (hWc : W ≤ Subgroup.centralizer ({a} : Set X))
    (hWp : Nat.Coprime p (Nat.card W)) (hBW : B ≤ Subgroup.normalizer (W : Set X))
    (hab : ∀ x ∈ X₁, ∀ y ∈ X₁, ⁅x, y⁆ ∈ K ⊔ W) :
    W ⊓ (⨅ (J : Subgroup X)
        (_ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J),
        Subgroup.normalizer (J : Set X)) ≤ Subgroup.centralizer (K : Set X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have haB : a ∈ B := hAB haA
  have hap : a ^ p = 1 := hBel.2 a haB
  have hX₁N : X₁ ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).1 hKn
  set Ca := Subgroup.centralizer ({a} : Set X) with hCa
  set C := X₁ ⊓ Ca with hC
  set R := GLAPPrimeCoreOf p C with hR
  set N := K ⊓ Ca with hN
  set W₁ := W ⊓ (⨅ (J : Subgroup X) (_ : GLAPComponent p N J), Subgroup.normalizer (J : Set X))
    with hW₁
  have hRK : R ≤ Subgroup.centralizer (K : Set X) :=
    core_le_centralizer hp hq hpK hKX hKn (hBX haB) haA ha1 hap hloc
  have hNC : N ≤ C := fun x hx => ⟨hKX hx.1, hx.2⟩
  have hNn : (N.subgroupOf C).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).2 fun c hc => ?_
    exact mem_normalizer_inf (hX₁N hc.1) (Subgroup.le_normalizer hc.2)
  have hNsub : IsSubnormal N C := isSubnormal_of_normal hNC hNn
  have haCa : ∀ b ∈ B, b ∈ Ca := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2 (CFSG.Open.IsElemAbelian.comm hBel haB hb).symm
  have hBC : B ≤ C := fun b hb => ⟨hBX hb, haCa b hb⟩
  have hWC : W ≤ C := fun w hw => ⟨hWX hw, hWc hw⟩
  have hW₁W : W₁ ≤ W := inf_le_left
  have hW₁C : W₁ ≤ C := hW₁W.trans hWC
  have hmemW₁ : ∀ w : X, w ∈ W₁ ↔ w ∈ W ∧ ∀ J : Subgroup X, GLAPComponent p N J →
      w ∈ Subgroup.normalizer (J : Set X) := by
    intro w
    simp only [hW₁, Subgroup.mem_inf, Subgroup.mem_iInf]
  have hBW₁ : B ≤ Subgroup.normalizer (W₁ : Set X) := by
    intro b hb
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    obtain ⟨hwW, hwJ⟩ := (hmemW₁ w).1 hw
    refine (hmemW₁ _).2 ⟨(Subgroup.mem_normalizer_iff.1 (hBW hb) w).1 hwW, fun J hJ => ?_⟩
    have hbJ := (hcomp J hJ).1 hb
    exact (Subgroup.normalizer (J : Set X)).mul_mem
      ((Subgroup.normalizer (J : Set X)).mul_mem hbJ (hwJ J hJ))
      ((Subgroup.normalizer (J : Set X)).inv_mem hbJ)
  have hW₁p : Nat.Coprime p (Nat.card W₁) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hW₁W) hWp
  have hJ' : ∀ J : Subgroup X, GLAPComponent p N J → ∀ w ∈ W₁, ∀ j ∈ J, w ∈ C →
      w * j * w⁻¹ * j⁻¹ ∈ GLAPPrimeCoreOf p C := by
    intro J hJ w hw j hj _
    have hsub : W₁ ≤ Subgroup.normalizer (J : Set X) ⊓ Ca := fun x hx =>
      ⟨((hmemW₁ x).1 hx).2 J hJ, hWc (((hmemW₁ x).1 hx).1)⟩
    have hlsb := (hcomp J hJ).2 W₁ hsub hW₁p (fun x hx => hBW₁ hx.1)
    have hmem : w * j * w⁻¹ * j⁻¹ ∈ ⁅J, W₁⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hw hj
    exact CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal hp
      (isSubnormal_trans hJ.2.1 hNsub) (hlsb hmem)
  set M := (K ⊔ W) ⊓ C with hM
  have hNM : N ≤ M := fun x hx => ⟨(le_sup_left : K ≤ K ⊔ W) hx.1, hNC hx⟩
  have hexp : ∀ x ∈ M, ∃ n : ℕ, Nat.Coprime p n ∧ x ^ n ∈ N := by
    intro x hx
    refine ⟨Nat.card W, hWp, ?_⟩
    exact ⟨pow_mem_of_mem_sup hWK hx.1, Subgroup.pow_mem _ hx.2.2 _⟩
  have hab' : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ M := by
    intro x hx y hy
    refine ⟨hab x hx.1 y hy.1, ?_⟩
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hx hy) (C.inv_mem hx)) (C.inv_mem hy)
  have hQcore : GLAPPrimeCore p (↥C ⧸ GLAPPrimeCore p ↥C) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hB' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf_of_le hSC hBC inf_le_left
  have hBbar : IsSCp p ⊤ (barX p C B) :=
    isSCp_map_quotient (GLAPPrimeCore p ↥C)
      ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card) hB'
  have hW₁bar_cop : Nat.Coprime p (Nat.card (barX p C W₁)) := by
    have h1 : Nat.card (barX p C W₁) ∣ Nat.card (W₁.subgroupOf C) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (W₁.subgroupOf C) = Nat.card W₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₁C).toEquiv
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 hW₁p
  have hBWbar : barX p C B ≤ Subgroup.normalizer (barX p C W₁ : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    barX_le_normalizer hBW₁
  have h1 := centralizes_pCore_of_isSCp_coprime input20_1_proved hp hp2 hBbar hW₁bar_cop hBWbar
  have h2 : ∀ L : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf L ⊤ →
      barX p C W₁ ≤ Subgroup.centralizer (L : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    fun L hL => barX_le_centralizer_components hp hNC hNn hNM hexp hab' hJ' L hL
  have hW₁bar : barX p C W₁ = ⊥ :=
    eq_bot_of_centralizes_pCore_components hp hQcore hW₁bar_cop h1 h2
  have hW₁R : W₁ ≤ R := by
    intro x hx
    have hxC : x ∈ C := hW₁C hx
    have hmem : (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) ⟨x, hxC⟩ ∈ barX p C W₁ :=
      ⟨⟨x, hxC⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩
    rw [hW₁bar, Subgroup.mem_bot] at hmem
    exact ⟨⟨x, hxC⟩, (QuotientGroup.eq_one_iff _).1 hmem, rfl⟩
  exact hW₁R.trans hRK

end CFSG.HardMathSupport.Dickson.I271
