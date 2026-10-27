module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I194Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.LStar
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs61
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Red
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.LocalAnalysis.ComponentInitial

section Helpers

theorem le_glaPPrimeCore_of_normal {H : Type*} [Group H] {p : ℕ} {K : Subgroup H}
    (hn : K.Normal) (hc : Nat.Coprime p (Nat.card K)) : K ≤ GLAPPrimeCore p H :=
  le_sSup ⟨hn, hc⟩

theorem le_glaPPrimeCoreOf {G : Type*} [Group G] {p : ℕ} {K T : Subgroup G} (hTK : T ≤ K)
    (hn : ∀ g ∈ K, ∀ t ∈ T, g * t * g⁻¹ ∈ T) (hc : Nat.Coprime p (Nat.card T)) :
    T ≤ GLAPPrimeCoreOf p K := by
  have hT' : (T.subgroupOf K).Normal := ⟨fun n hn' g => by
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    exact hn g g.2 n hn'⟩
  have hc' : Nat.Coprime p (Nat.card (T.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv]
    exact hc
  have hle : T.subgroupOf K ≤ GLAPPrimeCore p K := le_glaPPrimeCore_of_normal hT' hc'
  intro t ht
  exact Subgroup.mem_map.2 ⟨⟨t, hTK ht⟩, hle (Subgroup.mem_subgroupOf.2 ht), rfl⟩

theorem glaPPrimeCore_eq_bot_of_subnormal {p : ℕ} (hp : p.Prime) {Y : Type} [Group Y]
    [Finite Y] (hO : GLAPPrimeCore p Y = ⊥) {J : Subgroup Y} (hJ : IsSubnormal J ⊤) :
    GLAPPrimeCore p ↥J = ⊥ := by
  have htop : GLAPPrimeCore p ↥(⊤ : Subgroup Y) = ⊥ := by
    have h := CFSG.HardMathSupport.Timmesfeld.Balance.map_gLAPPrimeCore_mulEquiv p
      (Subgroup.topEquiv (G := Y))
    rw [hO] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.topEquiv (G := Y)).injective).1 h
  have hGtop : GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := by
    unfold GLAPPrimeCoreOf
    rw [htop, Subgroup.map_bot]
  have hGJ : GLAPPrimeCoreOf p J = ⊥ := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hJ, hGtop, inf_bot_eq]
  unfold GLAPPrimeCoreOf at hGJ
  exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 hGJ

theorem isPGroup_of_le_elemAbelian {p : ℕ} {Y : Type} [Group Y] {B : Subgroup Y}
    (hB : IsElemAbelian p B) {H : Subgroup Y} (hH : H ≤ B) : IsPGroup p ↥H := fun g => by
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using hB.2 (g : Y) (hH g.2)

theorem conj_mem_iSup_of_normalizes {Y : Type} [Group Y] {ι : Sort*} (K : ι → Subgroup Y)
    {g : Y} (hg : ∀ i, g ∈ Subgroup.normalizer (K i : Set Y)) :
    ∀ x ∈ (⨆ i, K i : Subgroup Y), g * x * g⁻¹ ∈ (⨆ i, K i : Subgroup Y) := by
  intro x hx
  refine Subgroup.iSup_induction K (C := fun x => g * x * g⁻¹ ∈ (⨆ i, K i : Subgroup Y))
    hx (fun i y hy => le_iSup K i (((Subgroup.mem_normalizer_iff.1 (hg i)) y).1 hy))
    ?_ ?_
  · simp
  · intro y z hy hz
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]
    exact (⨆ i, K i : Subgroup Y).mul_mem hy hz

theorem mem_normalizer_iSup {Y : Type} [Group Y] {ι : Sort*} (K : ι → Subgroup Y) {g : Y}
    (hg : ∀ i, g ∈ Subgroup.normalizer (K i : Set Y)) :
    g ∈ Subgroup.normalizer ((⨆ i, K i : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_mem_iSup_of_normalizes K hg h hh
  · intro hh
    have hg' : ∀ i, g⁻¹ ∈ Subgroup.normalizer (K i : Set Y) :=
      fun i => (Subgroup.normalizer (K i : Set Y)).inv_mem (hg i)
    have h3 := conj_mem_iSup_of_normalizes K hg' _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at h3

@[expose] noncomputable def restrictJ {Y : Type} [Group Y] (p : ℕ) (J L : Subgroup Y) :
    ↥(Subgroup.normalizer (L : Set Y) ⊓ Subgroup.normalizer (J : Set Y)) →*
      MulAut (barOf p J) :=
  (barAut p J).comp (Subgroup.inclusion inf_le_right)

@[expose] noncomputable def automizer {Y : Type} [Group Y] (L : Subgroup Y) :
    Subgroup (MulAut ↥L) :=
  (normalizerConjHom L).range

@[expose] noncomputable def actL {Y : Type} [Group Y] (L J : Subgroup Y) :
    ↥(Subgroup.normalizer (L : Set Y) ⊓ Subgroup.normalizer (J : Set Y)) →* ↥(automizer L) :=
  (normalizerConjHom L).rangeRestrict.comp (Subgroup.inclusion inf_le_left)

theorem restrictJ_mk {Y : Type} [Group Y] {p : ℕ} {J L : Subgroup Y}
    (n : ↥(Subgroup.normalizer (L : Set Y) ⊓ Subgroup.normalizer (J : Set Y))) (y : ↥J) :
    restrictJ p J L n (QuotientGroup.mk y) =
      QuotientGroup.mk (J.normalizerMonoidHom ⟨(n : Y), (Subgroup.mem_inf.1 n.2).2⟩ y) := by
  unfold restrictJ
  rw [MonoidHom.comp_apply, barAut_mk]
  rfl

theorem restrictJ_eq_one_iff {Y : Type} [Group Y] {p : ℕ} {J L : Subgroup Y}
    (hJ : GLAPPrimeCore p ↥J = ⊥)
    (n : ↥(Subgroup.normalizer (L : Set Y) ⊓ Subgroup.normalizer (J : Set Y))) :
    restrictJ p J L n = 1 ↔ ∀ y ∈ J, (n : Y) * y * (n : Y)⁻¹ = y := by
  constructor
  · intro h y hy
    have h1 := congrArg (fun f : MulAut (barOf p J) => f (QuotientGroup.mk ⟨y, hy⟩)) h
    simp only [MulAut.one_apply] at h1
    rw [restrictJ_mk, QuotientGroup.eq, hJ, Subgroup.mem_bot, inv_mul_eq_one] at h1
    have h3 := congrArg Subtype.val h1
    simpa using h3
  · intro h
    apply MulEquiv.ext
    intro z
    induction z using QuotientGroup.induction_on with
    | _ y =>
      rw [restrictJ_mk, MulAut.one_apply, QuotientGroup.eq, hJ, Subgroup.mem_bot, inv_mul_eq_one]
      apply Subtype.ext
      simpa using h y y.2

section OrbitLayer

variable {Y : Type} [Group Y]

theorem conj_mem_orbitLayer {A J : Subgroup Y} {a : Y} (ha : a ∈ A) :
    ∀ x ∈ orbitLayer A J, a * x * a⁻¹ ∈ orbitLayer A J := by
  intro x hx
  refine Subgroup.iSup_induction (fun b : A => conjJ (b : Y) J)
    (C := fun x => a * x * a⁻¹ ∈ orbitLayer A J) hx ?_ ?_ ?_
  · intro b y hy
    apply le_orbitLayer (⟨a * b, A.mul_mem ha b.2⟩ : A)
    show a * y * a⁻¹ ∈ conjJ (a * (b : Y)) J
    rw [mem_conjJ]
    have e : (a * (b : Y))⁻¹ * (a * y * a⁻¹) * (a * b) = (b : Y)⁻¹ * y * b := by group
    rw [e]
    exact mem_conjJ.1 hy
  · simp only [mul_one, mul_inv_cancel]
    exact (orbitLayer A J).one_mem
  · intro y z hy hz
    have e : a * (y * z) * a⁻¹ = (a * y * a⁻¹) * (a * z * a⁻¹) := by group
    rw [e]
    exact (orbitLayer A J).mul_mem hy hz

theorem mem_normalizer_orbitLayer_of_mem {A J : Subgroup Y} {a : Y} (ha : a ∈ A) :
    a ∈ Subgroup.normalizer ((orbitLayer A J : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_mem_orbitLayer ha h hh
  · intro hh
    have h3 := conj_mem_orbitLayer (A.inv_mem ha) _ hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rwa [e] at h3

theorem le_orbitLayer_self (A J : Subgroup Y) : J ≤ orbitLayer A J := by
  have h : conjJ 1 J ≤ orbitLayer A J := le_orbitLayer (⟨1, A.one_mem⟩ : A)
  rwa [conjJ_one] at h

end OrbitLayer

theorem h1_image_mem {X Z : Type} [Group X] [Finite X] [Group Z] {φ : X →* Z}
    (hφ : Function.Surjective φ) {p : ℕ} (hp : p.Prime) {Q T : Subgroup X} (hQ : IsPGroup p Q)
    (hTC : T ≤ Subgroup.centralizer (Q : Set X))
    (hTn : ∀ g ∈ Subgroup.centralizer (Q : Set X), ∀ t ∈ T, g * t * g⁻¹ ∈ T)
    (hTp : Nat.Coprime p (Nat.card T)) {t : X} (ht : t ∈ T) :
    φ t ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ((Q.map φ : Subgroup Z) : Set Z)) := by
  have h1 := CFSG.HardMathSupport.Solomon.Coordinator.h1Stmt_holds φ hφ hp hQ
  have hT := le_glaPPrimeCoreOf hTC hTn hTp ht
  exact h1 (Subgroup.mem_map.2 ⟨t, hT, rfl⟩)

theorem isPGroup_subgroupOf_of_pow {Y : Type} [Group Y] {p : ℕ} {A : Subgroup Y}
    (hA : ∀ x ∈ A, x ^ p = 1) (N : Subgroup Y) : IsPGroup p ↥(A.subgroupOf N) := fun x => by
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  simpa using hA ((x : N) : Y) (Subgroup.mem_subgroupOf.1 x.2)

end Helpers

theorem restrictJ_eq_one_of_actL {Y : Type} [Group Y] {p : ℕ} {J L : Subgroup Y}
    (hJL : J ≤ L) (hJ : GLAPPrimeCore p ↥J = ⊥)
    (n : ↥(Subgroup.normalizer (L : Set Y) ⊓ Subgroup.normalizer (J : Set Y)))
    (h : actL L J n = 1) : restrictJ p J L n = 1 := by
  rw [restrictJ_eq_one_iff hJ]
  intro y hy
  have h1 : normalizerConjHom L ⟨(n : Y), (Subgroup.mem_inf.1 n.2).1⟩ = 1 :=
    congrArg Subtype.val h
  have h2 := congrArg (fun f : MulAut ↥L => ((f ⟨y, hJL hy⟩ : ↥L) : Y)) h1
  simpa [coe_normalizerConjHom_apply] using h2

theorem glaPPrimeCoreOf_le_self {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) :
    GLAPPrimeCoreOf p H ≤ H := by
  rintro x hx
  have hx' : x ∈ (GLAPPrimeCore p ↥H).map H.subtype := hx
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx'
  exact y.2

theorem normalizerConjHom_comm_of_central {Y : Type} [Group Y] {L : Subgroup Y} {a x : Y}
    (ha : a ∈ Subgroup.normalizer (L : Set Y)) (hx : x ∈ Subgroup.normalizer (L : Set Y))
    (hc : a * x * a⁻¹ * x⁻¹ ∈ Subgroup.centralizer (L : Set Y)) :
    normalizerConjHom L ⟨a, ha⟩ * normalizerConjHom L ⟨x, hx⟩ =
      normalizerConjHom L ⟨x, hx⟩ * normalizerConjHom L ⟨a, ha⟩ := by
  refine MulEquiv.ext fun l => Subtype.ext ?_
  simp only [MulAut.mul_apply, coe_normalizerConjHom_apply]
  set c := a * x * a⁻¹ * x⁻¹ with hcdef
  have hm : x * (a * (l : Y) * a⁻¹) * x⁻¹ ∈ L := by
    have h1 : a * (l : Y) * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 ha _).1 l.2
    exact (Subgroup.mem_normalizer_iff.1 hx _).1 h1
  have hcm : c * (x * (a * (l : Y) * a⁻¹) * x⁻¹) = (x * (a * (l : Y) * a⁻¹) * x⁻¹) * c :=
    ((Subgroup.mem_centralizer_iff.1 hc) _ hm).symm
  calc a * (x * (l : Y) * x⁻¹) * a⁻¹
      = c * (x * (a * (l : Y) * a⁻¹) * x⁻¹) * c⁻¹ := by rw [hcdef]; group
    _ = (x * (a * (l : Y) * a⁻¹) * x⁻¹) := by rw [hcm]; group

theorem innerAut_normal_of (K : Type) [Group K] : (innerAut K).Normal := by
  constructor
  rintro _ ⟨g, rfl⟩ β
  refine ⟨β g, ?_⟩
  ext x
  simp [MulAut.conj_apply]

theorem normalizerConjHom_comm_of_mul_comm {Y : Type} [Group Y] {L : Subgroup Y} {a x : Y}
    (ha : a ∈ Subgroup.normalizer (L : Set Y)) (hx : x ∈ Subgroup.normalizer (L : Set Y))
    (h : a * x = x * a) :
    normalizerConjHom L ⟨a, ha⟩ * normalizerConjHom L ⟨x, hx⟩ =
      normalizerConjHom L ⟨x, hx⟩ * normalizerConjHom L ⟨a, ha⟩ := by
  apply normalizerConjHom_comm_of_central ha hx
  have h1 : a * x * a⁻¹ * x⁻¹ = 1 := by rw [h]; group
  rw [h1]
  exact Subgroup.one_mem _

theorem coe_eq_of_mk_eq {Y : Type} [Group Y] {p : ℕ} {J : Subgroup Y}
    (hJ : GLAPPrimeCore p ↥J = ⊥) {x y : ↥J}
    (h : (QuotientGroup.mk x : barOf p J) = QuotientGroup.mk y) : (x : Y) = y := by
  rw [QuotientGroup.eq, hJ, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact congrArg Subtype.val h

theorem orbit_centralizes {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p Y = ⊥) {B A : Subgroup Y} (hB : IsElemAbelian p B) (hAB : A ≤ B)
    (hcf : ∀ L : Subgroup Y, IsComponent L → IsCompCoreFreeLocalType p B L)
    {J : Subgroup Y} (hJ : IsComponent J) {w : Y}
    (hw : w ∈ GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set Y))) : ∀ y ∈ J, w * y = y * w := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨a, hAB ha⟩ ⟨b, hAB hb⟩)
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx => hB.2 x (hAB hx)
  have hApg : IsPGroup p ↥A := isPGroup_of_le_elemAbelian hB hAB
  set W := GLAPPrimeCoreOf p (Subgroup.centralizer (A : Set Y)) with hWdef
  have hWC : W ≤ Subgroup.centralizer (A : Set Y) := by
    rintro x hx
    have hx' : x ∈ (GLAPPrimeCore p ↥(Subgroup.centralizer (A : Set Y))).map
        (Subgroup.centralizer (A : Set Y)).subtype := hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx'
    exact y.2
  have hWnorm : ∀ g ∈ Subgroup.centralizer (A : Set Y), ∀ t ∈ W, g * t * g⁻¹ ∈ W := by
    intro g hg t ht
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p _ hg) t).1 ht
  have hWcop : Nat.Coprime p (Nat.card W) := coprime_card_GLAPPrimeCoreOf hp _
  have hWlstar : ∀ K : Subgroup Y, IsComponent K → ∀ t ∈ W,
      t ∈ Subgroup.normalizer (K : Set Y) := by
    intro K hK t ht
    have hKo : IsComponentOf K ⊤ := (isComponent_iff_open K).1 hK
    exact lstar_claim hO _ A hApg rfl K hKo ht
  have hJO : GLAPPrimeCore p ↥J = ⊥ :=
    glaPPrimeCore_eq_bot_of_subnormal hp hO ((isComponent_iff_open J).1 hJ).2.1
  set L := orbitLayer A J with hLdef
  have hJL : J ≤ L := le_orbitLayer_self A J
  have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer (L : Set Y) := fun a ha =>
    mem_normalizer_orbitLayer_of_mem ha
  have hWN : ∀ t ∈ W, t ∈ Subgroup.normalizer (L : Set Y) := fun t ht =>
    mem_normalizer_iSup (fun b : A => conjJ (b : Y) J)
      (fun b => hWlstar _ (isComponent_conjJ hJ (b : Y)) t ht)
  set N := Subgroup.normalizer (L : Set Y) with hNdef
  set Q : Subgroup N := A.subgroupOf N with hQdef
  have hQp : IsPGroup p ↥Q := isPGroup_subgroupOf_of_pow hApow N
  let φ' : ↥N →* ↥(automizer L) := (normalizerConjHom L).rangeRestrict
  have hφ'surj : Function.Surjective φ' := MonoidHom.rangeRestrict_surjective _
  set T : Subgroup N := W.subgroupOf N with hTdef
  have hTC : T ≤ Subgroup.centralizer (Q : Set N) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hq' : (q : Y) ∈ A := Subgroup.mem_subgroupOf.1 hq
    have ht' : (t : Y) ∈ W := Subgroup.mem_subgroupOf.1 ht
    exact (Subgroup.mem_centralizer_iff.1 (hWC ht')) (q : Y) hq'
  have hTn : ∀ g ∈ Subgroup.centralizer (Q : Set N), ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro g hg t ht
    have hgA : (g : Y) ∈ Subgroup.centralizer (A : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hq : (⟨a, hAN a ha⟩ : N) ∈ Q := Subgroup.mem_subgroupOf.2 ha
      have := congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hg) _ hq)
      exact this
    refine Subgroup.mem_subgroupOf.2 ?_
    exact hWnorm _ hgA _ (Subgroup.mem_subgroupOf.1 ht)
  have hTp : Nat.Coprime p (Nat.card T) := by
    have hle : T.map N.subtype ≤ W := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hx
    rw [← Subgroup.card_map_of_injective N.subtype_injective]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle) hWcop
  set M := GLAPPrimeCoreOf p (Subgroup.centralizer ((Q.map φ' : Subgroup ↥(automizer L)) :
    Set ↥(automizer L))) with hMdef
  have hWM : ∀ t (ht : t ∈ W), φ' ⟨t, hWN t ht⟩ ∈ M := fun t ht =>
    h1_image_mem hφ'surj hp hQp hTC hTn hTp (t := ⟨t, hWN t ht⟩) (Subgroup.mem_subgroupOf.2 ht)
  set NN : Subgroup Y := Subgroup.normalizer (L : Set Y) ⊓ Subgroup.normalizer (J : Set Y) with hNN
  have hANN : ∀ a ∈ A ⊓ Subgroup.normalizer (J : Set Y), a ∈ NN := fun a ha =>
    Subgroup.mem_inf.2 ⟨hAN a (Subgroup.mem_inf.1 ha).1, (Subgroup.mem_inf.1 ha).2⟩
  have hJNN : ∀ j ∈ J, j ∈ NN := fun j hj =>
    Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer (hJL hj), Subgroup.le_normalizer hj⟩
  have hψ_ker : ∀ n : ↥NN, actL L J n = 1 → restrictJ p J L n = 1 := fun n hn =>
    restrictJ_eq_one_of_actL hJL hJO n hn
  set Cz := Subgroup.centralizer ((Q.map φ' : Subgroup ↥(automizer L)) : Set ↥(automizer L))
    with hCz
  set CC : Subgroup ↥NN := Subgroup.comap (actL L J) Cz with hCC
  set PP : Subgroup ↥NN := Subgroup.comap (actL L J) M with hPP
  set AJ' : Subgroup ↥NN := (A ⊓ Subgroup.normalizer (J : Set Y)).subgroupOf NN with hAJ'
  have hζA : ∀ aa : ↥NN, (aa : Y) ∈ A ⊓ Subgroup.normalizer (J : Set Y) →
      actL L J aa ∈ (Q.map φ' : Subgroup ↥(automizer L)) := fun aa haa =>
    Subgroup.mem_map.2 ⟨⟨(aa : Y), hAN _ (Subgroup.mem_inf.1 haa).1⟩,
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 haa).1, rfl⟩
  have hFcomm : ∀ n ∈ CC, ∀ aa : ↥NN, (aa : Y) ∈ A ⊓ Subgroup.normalizer (J : Set Y) →
      restrictJ p J L n * restrictJ p J L aa = restrictJ p J L aa * restrictJ p J L n := by
    intro n hn aa haa
    have hn' : actL L J n ∈ Cz := hn
    have hcz : actL L J aa * actL L J n = actL L J n * actL L J aa :=
      (Subgroup.mem_centralizer_iff.1 hn') _ (hζA aa haa)
    have hnaa : actL L J (n * aa) = actL L J (aa * n) := by
      rw [map_mul, map_mul]
      exact hcz.symm
    have h1 : restrictJ p J L (n * aa * (aa * n)⁻¹) = 1 :=
      hψ_ker _ (by rw [map_mul, map_inv, hnaa, mul_inv_cancel])
    rw [map_mul, map_inv] at h1
    have h2 : restrictJ p J L (n * aa) = restrictJ p J L (aa * n) := mul_inv_eq_one.1 h1
    rw [← map_mul, ← map_mul]
    exact h2
  have hFlift : ∀ jj : ↥NN, (jj : Y) ∈ J →
      (∀ aa : ↥NN, (aa : Y) ∈ A ⊓ Subgroup.normalizer (J : Set Y) →
        restrictJ p J L jj * restrictJ p J L aa = restrictJ p J L aa * restrictJ p J L jj) →
      ∃ x ∈ CC, restrictJ p J L x = restrictJ p J L jj := by
    intro jj hjJ hcj
    have hcomm : ∀ a ∈ A, a ∈ Subgroup.normalizer (J : Set Y) → ∀ y ∈ J,
        a * ((jj : Y) * y * (jj : Y)⁻¹) * a⁻¹ = (jj : Y) * (a * y * a⁻¹) * (jj : Y)⁻¹ := by
      intro a ha haN y hy
      have haA : a ∈ A ⊓ Subgroup.normalizer (J : Set Y) := Subgroup.mem_inf.2 ⟨ha, haN⟩
      obtain ⟨aa, haa⟩ : ∃ aa : ↥NN, (aa : Y) = a := ⟨⟨a, hANN a haA⟩, rfl⟩
      have h := congrArg (fun f : MulAut (barOf p J) => f (QuotientGroup.mk ⟨y, hy⟩))
        (hcj aa (by rw [haa]; exact haA))
      simp only [MulAut.mul_apply, restrictJ_mk] at h
      have h' := coe_eq_of_mk_eq hJO h
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, haa] at h'
      exact h'.symm
    obtain ⟨x, hxL, hxN, hxy, hxc⟩ := exists_orbit_lift hJ hAcomm hjJ hcomm
    have hxN' : x ∈ NN := Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer hxL, hxN⟩
    refine ⟨⟨x, hxN'⟩, ?_, ?_⟩
    · show actL L J ⟨x, hxN'⟩ ∈ Cz
      rw [hCz, Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hz
      have hqA : (q : Y) ∈ A := Subgroup.mem_subgroupOf.1 hq
      apply Subtype.ext
      exact normalizerConjHom_comm_of_central (hAN _ hqA) (Subgroup.le_normalizer hxL) (hxc _ hqA)
    · apply MulEquiv.ext
      intro z
      induction z using QuotientGroup.induction_on with
      | _ y =>
        rw [restrictJ_mk, restrictJ_mk]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
        exact hxy y y.2
  set ψ := restrictJ p J L with hψdef
  have hAJCC : AJ' ≤ CC := by
    intro aa haa
    have haA : (aa : Y) ∈ A ⊓ Subgroup.normalizer (J : Set Y) := Subgroup.mem_subgroupOf.1 haa
    show actL L J aa ∈ Cz
    rw [hCz, Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hz
    have hqA : (q : Y) ∈ A := Subgroup.mem_subgroupOf.1 hq
    apply Subtype.ext
    exact normalizerConjHom_comm_of_mul_comm (hAN _ hqA) (Subgroup.mem_inf.1 (hANN _ haA)).1
      (hAcomm _ hqA _ (Subgroup.mem_inf.1 haA).1)
  have hCC_cent : ∀ s ∈ CC.map ψ, s ∈ Subgroup.centralizer ((AJ'.map ψ : Subgroup _) : Set _) := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hs
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨aa, haa, rfl⟩ := Subgroup.mem_map.1 hd
    exact (hFcomm c hc aa (Subgroup.mem_subgroupOf.1 haa)).symm
  set HH : Subgroup (MulAut (barOf p J)) := CC.map ψ ⊔ innerAut (barOf p J) with hHH
  haveI : (innerAut (barOf p J)).Normal := innerAut_normal_of _
  have hDH : AJ'.map ψ ≤ HH := (Subgroup.map_mono hAJCC).trans le_sup_left
  have hDN : AJ'.map ψ ≤ Subgroup.normalizer (HH : Set (MulAut (barOf p J))) :=
    hDH.trans Subgroup.le_normalizer
  have hD_auto : AJ'.map ψ ≤ autBar p B J := by
    rintro _ ⟨aa, haa, rfl⟩
    have haA : (aa : Y) ∈ A ⊓ Subgroup.normalizer (J : Set Y) := Subgroup.mem_subgroupOf.1 haa
    unfold autBar
    exact Subgroup.mem_map.2 ⟨⟨(aa : Y), (Subgroup.mem_inf.1 haA).2⟩,
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hAB (Subgroup.mem_inf.1 haA).1,
        (Subgroup.mem_inf.1 haA).2⟩), rfl⟩
  have hcore : GLAPPrimeCoreOf p (HH ⊓ Subgroup.centralizer ((AJ'.map ψ : Subgroup _) :
      Set (MulAut (barOf p J)))) = ⊥ :=
    hcf J hJ (AJ'.map ψ) hD_auto HH le_sup_right hDN
  have hHC : HH ⊓ Subgroup.centralizer ((AJ'.map ψ : Subgroup _) : Set (MulAut (barOf p J))) ≤
      CC.map ψ := by
    rintro g ⟨hgH, hgC⟩
    obtain ⟨s, hs, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hgH
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hs
    have hsC : ψ c ∈ Subgroup.centralizer ((AJ'.map ψ : Subgroup _) : Set (MulAut (barOf p J))) :=
      hCC_cent _ (Subgroup.mem_map.2 ⟨c, hc, rfl⟩)
    have hzC : z ∈ Subgroup.centralizer ((AJ'.map ψ : Subgroup _) : Set (MulAut (barOf p J))) := by
      have := (Subgroup.centralizer ((AJ'.map ψ : Subgroup _) : Set (MulAut (barOf p J)))).mul_mem
        (Subgroup.inv_mem _ hsC) hgC
      simpa using this
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.1 hz
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective q
    have hψjj : ψ ⟨(x' : Y), hJNN _ x'.2⟩ = MulAut.conj (QuotientGroup.mk x') := by
      apply MulEquiv.ext
      intro w
      induction w using QuotientGroup.induction_on with
      | _ y =>
        rw [restrictJ_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
          ← QuotientGroup.mk_mul]
        congr 1
    have hzC' : ∀ aa : ↥NN, (aa : Y) ∈ A ⊓ Subgroup.normalizer (J : Set Y) →
        restrictJ p J L ⟨(x' : Y), hJNN _ x'.2⟩ * restrictJ p J L aa =
          restrictJ p J L aa * restrictJ p J L ⟨(x' : Y), hJNN _ x'.2⟩ := by
      intro aa haa
      have hmem : ψ aa ∈ AJ'.map ψ := Subgroup.mem_map.2 ⟨aa, Subgroup.mem_subgroupOf.2 haa, rfl⟩
      have := (Subgroup.mem_centralizer_iff.1 hzC) (ψ aa) hmem
      rw [hψjj]
      exact this.symm
    obtain ⟨x, hx, hxψ⟩ := hFlift ⟨(x' : Y), hJNN _ x'.2⟩ x'.2 hzC'
    refine Subgroup.mem_map.2 ⟨c * x, CC.mul_mem hc hx, ?_⟩
    rw [map_mul, hxψ, hψjj]
  have hMCz : GLAPPrimeCoreOf p Cz ≤ Cz := glaPPrimeCoreOf_le_self p Cz
  have hPP_CC : PP ≤ CC := fun n hn => hMCz (Subgroup.mem_comap.1 hn)
  have hPPsub : PP.map ψ ≤ HH ⊓ Subgroup.centralizer ((AJ'.map ψ : Subgroup _) :
      Set (MulAut (barOf p J))) := by
    rintro _ ⟨n, hn, rfl⟩
    have hnC : ψ n ∈ CC.map ψ := Subgroup.mem_map.2 ⟨n, hPP_CC hn, rfl⟩
    exact ⟨Subgroup.mem_sup_left hnC, hCC_cent _ hnC⟩
  have hPP_norm : ∀ g ∈ HH ⊓ Subgroup.centralizer ((AJ'.map ψ : Subgroup _) :
      Set (MulAut (barOf p J))), ∀ t ∈ PP.map ψ, g * t * g⁻¹ ∈ PP.map ψ := by
    intro g hg t ht
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 (hHC hg)
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 ht
    refine Subgroup.mem_map.2 ⟨c * n * c⁻¹, ?_, ?_⟩
    · have hcN := le_normalizer_glaPPrimeCoreOf p Cz (show actL L J c ∈ Cz from hc)
      show actL L J (c * n * c⁻¹) ∈ M
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hcN _).1 hn
    · rw [map_mul, map_mul, map_inv]
  have hPP_card : Nat.Coprime p (Nat.card ↥(PP.map ψ)) := by
    by_contra hnc
    have hdvd : p ∣ Nat.card ↥(PP.map ψ) := by
      rwa [Nat.Prime.coprime_iff_not_dvd hp, not_not] at hnc
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(PP.map ψ)) p hdvd
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.1 x.2
    have hord : orderOf (ψ n) = p := by
      rw [hnx, Subgroup.orderOf_coe, hx]
    have hk : actL L J (n ^ orderOf (actL L J n)) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    have hdiv1 : orderOf (ψ n) ∣ orderOf (actL L J n) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      exact hψ_ker _ hk
    rw [hord] at hdiv1
    have hnM : actL L J n ∈ GLAPPrimeCoreOf p Cz := hn
    have hcop : Nat.Coprime (orderOf (actL L J n)) p :=
      orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hnM
    have h1 : Nat.Coprime p p := Nat.Coprime.coprime_dvd_left hdiv1 hcop
    exact hp.one_lt.ne' ((Nat.coprime_self p).1 h1)
  have hbot : PP.map ψ ≤ ⊥ := by
    have := le_glaPPrimeCoreOf hPPsub hPP_norm hPP_card
    rw [hcore] at this
    exact this
  have hwJ : w ∈ Subgroup.normalizer (J : Set Y) := hWlstar J hJ w hw
  have hwP : (⟨w, Subgroup.mem_inf.2 ⟨hWN w hw, hwJ⟩⟩ : ↥NN) ∈ PP := hWM w hw
  have hψw : ψ ⟨w, Subgroup.mem_inf.2 ⟨hWN w hw, hwJ⟩⟩ = 1 :=
    Subgroup.mem_bot.1 (hbot (Subgroup.mem_map.2 ⟨_, hwP, rfl⟩))
  have hwy := (restrictJ_eq_one_iff hJO _).1 hψw
  intro y hy
  have h := hwy y hy
  calc w * y = w * y * w⁻¹ * w := by group
    _ = y * w := by rw [h]

end CFSG.LocalAnalysis.GLTheoremA
