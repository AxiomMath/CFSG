module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4.FaithfulA5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement IsMulCommutative

theorem natCard_linearEquiv_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] :
    Nat.card (V ≃ₗ[ZMod 2] V) = Nat.card (GL (Fin (Module.finrank (ZMod 2) V)) (ZMod 2)) := by
  have e : V ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) V) → ZMod 2) :=
    LinearEquiv.ofFinrankEq V _ (by rw [Module.finrank_fin_fun])
  rw [← Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toEquiv,
    Nat.card_congr (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toEquiv,
    Nat.card_congr (Matrix.GeneralLinearGroup.toLin).toEquiv]

theorem not_sixty_dvd_natCard_linearEquiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hV : Module.finrank (ZMod 2) V ≤ 3) :
    ¬ 60 ∣ Nat.card (V ≃ₗ[ZMod 2] V) := by
  rw [natCard_linearEquiv_zmod_two, Matrix.card_GL_field]
  generalize Module.finrank (ZMod 2) V = d at hV ⊢
  interval_cases d <;> simp [Fin.prod_univ_succ, ZMod.card] <;> norm_num

theorem sixteen_le_natCard_of_sixty_dvd {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] (h : 60 ∣ Nat.card (M ≃ₗ[ZMod 2] M)) : 16 ≤ Nat.card M := by
  have hd : 4 ≤ Module.finrank (ZMod 2) M := by
    by_contra hlt
    exact not_sixty_dvd_natCard_linearEquiv (V := M) (by omega) h
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ Module.finrank (ZMod 2) M := Nat.pow_le_pow_right (by norm_num) hd

theorem isSimpleGroup_and_card_of_isL2Quot {X : Type} [Group X] (hq : IsL2Quot 2 X) :
    IsSimpleGroup X ∧ Nat.card X = 60 := by
  have hcard : Nat.card X = 60 := by
    rw [hq.card (by norm_num)]
    norm_num
  obtain ⟨e⟩ := hq
  have hF4 : 4 ≤ Nat.card (GaloisField 2 2) := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
  exact ⟨e.isSimpleGroup, hcard⟩

class SecOK {G : Type} [Group G] (Y Z : Subgroup G) : Prop where
  comm : ∀ a ∈ Y, ∀ b ∈ Y, ⁅a, b⁆ ∈ Z
  sq : ∀ a ∈ Y, a ^ 2 ∈ Z

section Sec

variable {G : Type} [Group G]

instance secOK_normal (Y Z : Subgroup G) [SecOK Y Z] : (Z.subgroupOf Y).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : ⁅(g : G), (n : G)⁆ ∈ Z := SecOK.comm _ g.2 _ n.2
    have e : (g : G) * n * (g : G)⁻¹ = ⁅(g : G), (n : G)⁆ * n := by
      simp only [commutatorElement_def]; group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact Z.mul_mem hc hn

instance secOK_isMulCommutative (Y Z : Subgroup G) [SecOK Y Z] :
    IsMulCommutative (↥Y ⧸ Z.subgroupOf Y) := by
  refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
  show ⁅(⊤ : Subgroup ↥Y), ⊤⁆ ≤ Z.subgroupOf Y
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_subgroupOf]
  have := SecOK.comm (Y := Y) (Z := Z) (a : G) a.2 (b : G) b.2
  simpa [commutatorElement_def] using this

instance secOK_module (Y Z : Subgroup G) [SecOK Y Z] :
    Module (ZMod 2) (Additive (↥Y ⧸ Z.subgroupOf Y)) :=
  AddCommGroup.zmodModule (n := 2) (fun x => by
    apply toMul_eq_one.mp
    rw [toMul_nsmul]
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective x.toMul
    rw [← ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using SecOK.sq (Y := Y) (Z := Z) (a : G) a.2)

@[expose] def secMk (Y Z : Subgroup G) [SecOK Y Z] (y : ↥Y) : Additive (↥Y ⧸ Z.subgroupOf Y) :=
  Additive.ofMul (QuotientGroup.mk y)

theorem secMk_eq_iff (Y Z : Subgroup G) [SecOK Y Z] (y y' : ↥Y) :
    secMk Y Z y = secMk Y Z y' ↔ y⁻¹ * y' ∈ Z.subgroupOf Y := by
  unfold secMk
  rw [Additive.ofMul.injective.eq_iff, QuotientGroup.eq]

theorem exists_secMk (Y Z : Subgroup G) [SecOK Y Z] (v : Additive (↥Y ⧸ Z.subgroupOf Y)) :
    ∃ y : ↥Y, secMk Y Z y = v := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective v.toMul
  exact ⟨y, by unfold secMk; rw [hy]; rfl⟩

@[expose] def conjSub (Y : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    ↥Y ≃* ↥Y where
  toFun y := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp y.2⟩
  invFun y := ⟨g⁻¹ * y * g, (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (by
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [e]
    exact y.2)⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem coe_conjSub (Y : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (Y : Set G))
    (y : ↥Y) : ((conjSub Y g hg y : ↥Y) : G) = g * y * g⁻¹ := rfl

theorem map_conjSub_subgroupOf (Y Z : Subgroup G) [SecOK Y Z] (g : G)
    (hY : g ∈ Subgroup.normalizer (Y : Set G)) (hZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    (Z.subgroupOf Y).map (conjSub Y g hY).toMonoidHom = Z.subgroupOf Y := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.mem_normalizer_iff.mp hZ (((conjSub Y g hY).symm x : ↥Y) : G)
  have h2 : g * (((conjSub Y g hY).symm x : ↥Y) : G) * g⁻¹ = (x : G) := by
    have e : ((conjSub Y g hY).symm x : ↥Y) = ⟨g⁻¹ * x * g, _⟩ := rfl
    rw [e]
    simp only [mul_assoc]
    group
  rw [h2] at h1
  exact h1

theorem secMk_sub (Y Z : Subgroup G) [SecOK Y Z] (a b : ↥Y) :
    secMk Y Z a - secMk Y Z b = secMk Y Z (a * b⁻¹) := by
  unfold secMk
  rw [← ofMul_div, div_eq_mul_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

@[expose] def secWSet (Y X Z : Subgroup G) [SecOK Y Z] : Set (Additive (↥Y ⧸ Z.subgroupOf Y)) :=
  {v | ∃ x : ↥Y, (x : G) ∈ X ∧ v = secMk Y Z x}

@[expose] def secEquiv (Y Z : Subgroup G) [SecOK Y Z] (g : G)
    (hY : g ∈ Subgroup.normalizer (Y : Set G)) (hZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    Additive (↥Y ⧸ Z.subgroupOf Y) ≃ₗ[ZMod 2] Additive (↥Y ⧸ Z.subgroupOf Y) :=
  (QuotientGroup.congr (Z.subgroupOf Y) (Z.subgroupOf Y) (conjSub Y g hY)
    (map_conjSub_subgroupOf Y Z g hY hZ)).toAdditive.toLinearEquiv (fun c x => ZMod.map_smul _ c x)

theorem secEquiv_secMk (Y Z : Subgroup G) [SecOK Y Z] (g : G)
    (hY : g ∈ Subgroup.normalizer (Y : Set G)) (hZ : g ∈ Subgroup.normalizer (Z : Set G))
    (y : ↥Y) : secEquiv Y Z g hY hZ (secMk Y Z y) = secMk Y Z (conjSub Y g hY y) := rfl

theorem secEquiv_mul_apply (Y Z : Subgroup G) [SecOK Y Z] (g h : G)
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hh : h ∈ Subgroup.normalizer (Y : Set G)) (hhZ : h ∈ Subgroup.normalizer (Z : Set G))
    (v : Additive (↥Y ⧸ Z.subgroupOf Y)) :
    secEquiv Y Z (g * h) (mul_mem hg hh) (mul_mem hgZ hhZ) v =
      secEquiv Y Z g hg hgZ (secEquiv Y Z h hh hhZ v) := by
  obtain ⟨y, rfl⟩ := exists_secMk Y Z v
  simp only [secEquiv_secMk]
  congr 1
  ext
  simp only [coe_conjSub]
  group

@[expose] def secRho (L Y Z : Subgroup G) [SecOK Y Z] (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) :
    ↥L →* (Additive (↥Y ⧸ Z.subgroupOf Y) ≃ₗ[ZMod 2] Additive (↥Y ⧸ Z.subgroupOf Y)) :=
  MonoidHom.mk' (fun g => secEquiv Y Z (g : G) (hLY g.2) (hLZ g.2)) (by
    intro a b
    apply LinearEquiv.ext
    intro v
    exact secEquiv_mul_apply Y Z (a : G) (b : G) (hLY a.2) (hLZ a.2) (hLY b.2) (hLZ b.2) v)

theorem secRho_apply (L Y Z : Subgroup G) [SecOK Y Z] (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) (g : ↥L)
    (v : Additive (↥Y ⧸ Z.subgroupOf Y)) :
    secRho L Y Z hLY hLZ g v = secEquiv Y Z (g : G) (hLY g.2) (hLZ g.2) v := rfl

theorem secRho_eq_one_iff (L Y Z : Subgroup G) [SecOK Y Z]
    (hLY : L ≤ Subgroup.normalizer (Y : Set G)) (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) (g : ↥L) :
    secRho L Y Z hLY hLZ g = 1 ↔ ∀ y ∈ Y, y⁻¹ * ((g : G) * y * (g : G)⁻¹) ∈ Z := by
  constructor
  · intro h y hy
    have hv : secRho L Y Z hLY hLZ g (secMk Y Z ⟨y, hy⟩) = secMk Y Z ⟨y, hy⟩ := by
      rw [h]
      rfl
    rw [secRho_apply, secEquiv_secMk, eq_comm, secMk_eq_iff, Subgroup.mem_subgroupOf] at hv
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSub] at hv
    exact hv
  · intro h
    apply LinearEquiv.ext
    intro v
    obtain ⟨y, rfl⟩ := exists_secMk Y Z v
    show secRho L Y Z hLY hLZ g (secMk Y Z y) = secMk Y Z y
    rw [secRho_apply, secEquiv_secMk, secMk_eq_iff, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSub]
    have h' := Z.inv_mem (h (y : G) y.2)
    rw [mul_inv_rev, inv_inv] at h'
    exact h'

theorem action_trivial_or_faithful {Γ : Type} [Group Γ] (hq : IsL2Quot 2 (oTwoQuot Γ))
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (ρ : Γ →* (M ≃ₗ[ZMod 2] M)) (hρ : ∀ q ∈ pCore 2 Γ, ρ q = 1) :
    (∀ g : Γ, ρ g = 1) ∨ (16 ≤ Nat.card M ∧ ∀ g : Γ, ρ g = 1 → g ∈ pCore 2 Γ) := by
  obtain ⟨hsimp, hcard⟩ := isSimpleGroup_and_card_of_isL2Quot hq
  let ρbar : oTwoQuot Γ →* (M ≃ₗ[ZMod 2] M) :=
    QuotientGroup.lift (pCore 2 Γ) ρ (by
      intro q hq'
      exact MonoidHom.mem_ker.mpr (hρ q hq'))
  have hbar : ∀ g : Γ, ρbar (g : oTwoQuot Γ) = ρ g := fun g => rfl
  rcases hsimp.eq_bot_or_eq_top_of_normal ρbar.ker with hk | hk
  · have hinj : Function.Injective ρbar := (MonoidHom.ker_eq_bot_iff ρbar).mp hk
    have hdvd : Nat.card (oTwoQuot Γ) ∣ Nat.card (M ≃ₗ[ZMod 2] M) :=
      Subgroup.card_dvd_of_injective ρbar hinj
    rw [hcard] at hdvd
    refine Or.inr ⟨sixteen_le_natCard_of_sixty_dvd hdvd, fun g hg => ?_⟩
    have h1 : ρbar (g : oTwoQuot Γ) = 1 := by rw [hbar]; exact hg
    have h2 : (g : oTwoQuot Γ) = 1 := hinj (h1.trans (map_one ρbar).symm)
    exact (QuotientGroup.eq_one_iff g).mp h2
  · left
    intro g
    have hg : (g : oTwoQuot Γ) ∈ ρbar.ker := by
      rw [hk]
      exact Subgroup.mem_top _
    have h1 : ρbar (g : oTwoQuot Γ) = 1 := MonoidHom.mem_ker.mp hg
    rwa [hbar] at h1

theorem section_dichotomy {L Y Z : Subgroup G} [Finite G] [SecOK Y Z]
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hcore : ∀ q ∈ pCore 2 ↥L, ∀ y ∈ Y, y⁻¹ * ((q : G) * y * (q : G)⁻¹) ∈ Z) :
    (∀ g : ↥L, ∀ y ∈ Y, y⁻¹ * ((g : G) * y * (g : G)⁻¹) ∈ Z) ∨
      (16 ≤ Z.relIndex Y ∧
        ∀ g : ↥L, (∀ y ∈ Y, y⁻¹ * ((g : G) * y * (g : G)⁻¹) ∈ Z) → g ∈ pCore 2 ↥L) := by
  have hρ : ∀ q ∈ pCore 2 ↥L, secRho L Y Z hLY hLZ q = 1 :=
    fun q hq' => (secRho_eq_one_iff L Y Z hLY hLZ q).mpr (hcore q hq')
  rcases action_trivial_or_faithful hq (secRho L Y Z hLY hLZ) hρ with h | ⟨h16, hmem⟩
  · exact Or.inl fun g => (secRho_eq_one_iff L Y Z hLY hLZ g).mp (h g)
  · refine Or.inr ⟨?_, fun g hg => hmem g ((secRho_eq_one_iff L Y Z hLY hLZ g).mpr hg)⟩
    have e1 : Z.relIndex Y = Nat.card (Additive (↥Y ⧸ Z.subgroupOf Y)) := by
      rw [← Nat.card_congr Additive.ofMul]
      exact (Subgroup.index_eq_card _).symm
    rw [e1]
    exact h16

theorem pCoreOf_le_self (p : ℕ) {G : Type} [Group G] (H : Subgroup G) : pCoreOf p H ≤ H := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.2

theorem pCoreOf_le_of_normalizes {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hLP : L ≤ P) (hPL : P ≤ Subgroup.normalizer (L : Set G)) : pCoreOf 2 L ≤ pCoreOf 2 P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar := Subgroup.characteristic_iff_map_le.mp (CFSG.pCore_characteristic (p := 2) (G := ↥L))
  have hsub : ∀ p ∈ P, ∀ h ∈ pCoreOf 2 L, p * h * p⁻¹ ∈ pCoreOf 2 L := by
    intro p hp h hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hh
    have hx' : conjSub L p (hPL hp) x ∈ pCore 2 ↥L :=
      hchar (conjSub L p (hPL hp)) (Subgroup.mem_map_of_mem (conjSub L p (hPL hp)).toMonoidHom hx)
    have hy := Subgroup.mem_map_of_mem L.subtype hx'
    have e : L.subtype (conjSub L p (hPL hp) x) = p * (x : G) * p⁻¹ := rfl
    rw [e] at hy
    exact hy
  have hNP : pCoreOf 2 L ≤ P := (pCoreOf_le_self 2 L).trans hLP
  have hPN : P ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hsub p hp h hh
    · intro hh
      have h' := hsub p⁻¹ (P.inv_mem hp) _ hh
      have e : p⁻¹ * (p * h * p⁻¹) * p⁻¹⁻¹ = h := by group
      rwa [e] at h'
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNP hPN
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem coe_mem_pCoreOf_of_mem_pCore {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hLP : L ≤ P) (hPL : P ≤ Subgroup.normalizer (L : Set G)) {q : ↥L}
    (hq : q ∈ pCore 2 ↥L) : (q : G) ∈ pCoreOf 2 P :=
  pCoreOf_le_of_normalizes hLP hPL (Subgroup.mem_map_of_mem L.subtype hq)

theorem comm_of_fixes {M : Type*} [AddCommGroup M] (W : Set M) (A B : M → M)
    (hA : ∀ x y, A (x + y) = A x + A y) (hB : ∀ x y, B (x + y) = B x + B y)
    (hAW : ∀ w ∈ W, A w = w) (hBW : ∀ w ∈ W, B w = w)
    (hAs : ∀ v, A v - v ∈ W) (hBs : ∀ v, B v - v ∈ W) (v : M) : A (B v) = B (A v) := by
  have ha := hAs v
  have hb := hBs v
  have h1 : A (B v) = A v + (B v - v) := by
    calc A (B v) = A (v + (B v - v)) := by congr 1; abel
      _ = A v + A (B v - v) := hA _ _
      _ = A v + (B v - v) := by rw [hAW _ hb]
  have h2 : B (A v) = B v + (A v - v) := by
    calc B (A v) = B (v + (A v - v)) := by congr 1; abel
      _ = B v + B (A v - v) := hB _ _
      _ = B v + (A v - v) := by rw [hBW _ ha]
  rw [h1, h2]
  abel

end Sec

end CFSG.GH74.QTGen4.DSGen4.FaithfulA5

namespace CFSG.GH74.QTGen4.DSGen4

open FaithfulA5
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement IsMulCommutative

theorem leafFaithfulA5 : LeafFaithfulA5 := by
  intro G _ _ P L E K hLP hPL hEP hPE hPK hsec hcard hq hcore hnt
  have hLE : L ≤ Subgroup.normalizer (E : Set G) := fun l hl => hPE (hLP hl)
  have hLK : L ≤ Subgroup.normalizer (K : Set G) := fun l hl => hPK (hLP hl)
  haveI hEK : SecOK E K :=
    ⟨fun a ha b hb => hsec.2.1 (Subgroup.commutator_mem_commutator ha hb),
      fun a ha => hsec.2.2 a ha⟩
  have hcoreL : ∀ q ∈ pCore 2 ↥L, ∀ y ∈ E, y⁻¹ * ((q : G) * y * (q : G)⁻¹) ∈ K := by
    intro q hq' y hy
    have h1 := hcore (q : G) (coe_mem_pCoreOf_of_mem_pCore hLP hPL hq') y⁻¹ (E.inv_mem hy)
    have h2 := K.inv_mem h1
    have e : ⁅(q : G), y⁻¹⁆⁻¹ = y⁻¹ * ((q : G) * y * (q : G)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e] at h2
    exact h2
  have hnontriv : ¬ ∀ g : ↥L, ∀ y ∈ E, y⁻¹ * ((g : G) * y * (g : G)⁻¹) ∈ K := by
    intro h
    obtain ⟨l, hl, e, he, hne⟩ := hnt
    apply hne
    have h1 : e⁻¹⁻¹ * (l * e⁻¹ * l⁻¹) ∈ K := h ⟨l, hl⟩ e⁻¹ (E.inv_mem he)
    have h2 := K.inv_mem h1
    have e' : ⁅l, e⁆ = (e⁻¹⁻¹ * (l * e⁻¹ * l⁻¹))⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e']
    exact h2
  have hdichE := section_dichotomy (L := L) (Y := E) (Z := K) hq hLE hLK hcoreL
  have hcardE : K.relIndex E = 16 ∧
      ∀ g : ↥L, (∀ y ∈ E, y⁻¹ * ((g : G) * y * (g : G)⁻¹) ∈ K) → g ∈ pCore 2 ↥L := by
    rcases hdichE with h | ⟨h16, hmem⟩
    · exact absurd h hnontriv
    · exact ⟨le_antisymm hcard h16, hmem⟩
  obtain ⟨hcardEq, hmemE⟩ := hcardE
  refine ⟨hLP, hPL, hEP, hPE, hPK, hsec, hcardEq, ?_, hcore, hq, hnt⟩
  intro X hKX hXE hPX
  by_contra hne
  obtain ⟨hXK, hXE'⟩ := not_or.mp hne
  have hLX : L ≤ Subgroup.normalizer (X : Set G) := fun l hl => hPX (hLP hl)
  haveI hXK' : SecOK X K :=
    ⟨fun a ha b hb => SecOK.comm (Y := E) (Z := K) a (hXE ha) b (hXE hb),
      fun a ha => SecOK.sq (Y := E) (Z := K) a (hXE ha)⟩
  haveI hEX : SecOK E X :=
    ⟨fun a ha b hb => hKX (SecOK.comm (Y := E) (Z := K) a ha b hb),
      fun a ha => hKX (SecOK.sq (Y := E) (Z := K) a ha)⟩
  have hcoreX : ∀ q ∈ pCore 2 ↥L, ∀ y ∈ X, y⁻¹ * ((q : G) * y * (q : G)⁻¹) ∈ K :=
    fun q hq' y hy => hcoreL q hq' y (hXE hy)
  have hcoreEX : ∀ q ∈ pCore 2 ↥L, ∀ y ∈ E, y⁻¹ * ((q : G) * y * (q : G)⁻¹) ∈ X :=
    fun q hq' y hy => hKX (hcoreL q hq' y hy)
  have hdX := section_dichotomy (L := L) (Y := X) (Z := K) hq hLX hLK hcoreX
  have hdEX := section_dichotomy (L := L) (Y := E) (Z := X) hq hLE hLX hcoreEX
  have hprod : K.relIndex X * X.relIndex E = 16 := by
    rw [Subgroup.relIndex_mul_relIndex K X E hKX hXE, hcardEq]
  have hK1 : K.relIndex X ≠ 1 := fun h => hXK (le_antisymm (Subgroup.relIndex_eq_one.mp h) hKX)
  have hE1 : X.relIndex E ≠ 1 := fun h => hXE' (le_antisymm hXE (Subgroup.relIndex_eq_one.mp h))
  have hK0 : K.relIndex X ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    norm_num at hprod
  have hE0 : X.relIndex E ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    norm_num at hprod
  have hK2 : 2 ≤ K.relIndex X := by omega
  have hE2 : 2 ≤ X.relIndex E := by omega
  have hA8 : K.relIndex X ≤ 8 := by
    have h := Nat.mul_le_mul_left (K.relIndex X) hE2
    rw [hprod] at h
    omega
  have hB8 : X.relIndex E ≤ 8 := by
    have h := Nat.mul_le_mul_right (X.relIndex E) hK2
    rw [hprod] at h
    omega
  have hAfix : ∀ g : ↥L, ∀ y ∈ X, y⁻¹ * ((g : G) * y * (g : G)⁻¹) ∈ K := by
    rcases hdX with h | ⟨h16, _⟩
    · exact h
    · omega
  have hBfix : ∀ g : ↥L, ∀ y ∈ E, y⁻¹ * ((g : G) * y * (g : G)⁻¹) ∈ X := by
    rcases hdEX with h | ⟨h16, _⟩
    · exact h
    · omega
  have hfixW : ∀ g : ↥L, ∀ w ∈ secWSet E X K, secRho L E K hLE hLK g w = w := by
    rintro g w ⟨x, hxX, rfl⟩
    rw [secRho_apply, secEquiv_secMk, secMk_eq_iff, Subgroup.mem_subgroupOf]
    have h1 := K.inv_mem (hAfix g (x : G) hxX)
    rw [mul_inv_rev, inv_inv] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSub]
    exact h1
  have hsubW : ∀ g : ↥L, ∀ v, secRho L E K hLE hLK g v - v ∈ secWSet E X K := by
    intro g v
    obtain ⟨e, rfl⟩ := exists_secMk E K v
    rw [secRho_apply, secEquiv_secMk, secMk_sub]
    refine ⟨conjSub E (g : G) (hLE g.2) e * e⁻¹, ?_, rfl⟩
    have h1 := X.inv_mem (hBfix g (e : G)⁻¹ (E.inv_mem e.2))
    convert h1 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSub]
    group
  have hcommρ : ∀ g h : ↥L, ∀ v, secRho L E K hLE hLK g (secRho L E K hLE hLK h v) =
      secRho L E K hLE hLK h (secRho L E K hLE hLK g v) := fun g h v =>
    comm_of_fixes (secWSet E X K) (secRho L E K hLE hLK g) (secRho L E K hLE hLK h)
      (fun x y => map_add _ x y) (fun x y => map_add _ x y) (hfixW g) (hfixW h)
      (hsubW g) (hsubW h) v
  have hcommGroup : ∀ g h : ↥L, secRho L E K hLE hLK g * secRho L E K hLE hLK h =
      secRho L E K hLE hLK h * secRho L E K hLE hLK g := by
    intro g h
    apply LinearEquiv.ext
    intro v
    exact hcommρ g h v
  have hcommutatorCore : ∀ g h : ↥L, ⁅g, h⁆ ∈ pCore 2 ↥L := by
    intro g h
    have h1 : secRho L E K hLE hLK ⁅g, h⁆ = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hcommGroup g h]
      group
    exact hmemE _ ((secRho_eq_one_iff L E K hLE hLK ⁅g, h⁆).mp h1)
  haveI hcommQ : IsMulCommutative (oTwoQuot ↥L) := by
    refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
    show ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ pCore 2 ↥L
    rw [Subgroup.commutator_le]
    intro g _ h _
    exact hcommutatorCore g h
  obtain ⟨hsimp, hcard60⟩ := isSimpleGroup_and_card_of_isL2Quot hq
  have hprime := (Group.is_simple_iff_prime_card (α := oTwoQuot ↥L)).mp hsimp
  rw [hcard60] at hprime
  norm_num at hprime

end CFSG.GH74.QTGen4.DSGen4
