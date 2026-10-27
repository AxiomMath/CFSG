module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Y
public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Char
public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Sigma3
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.Quasithin.Background.B2FactorizationSolvable

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace L97

open Sigma3

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_conjClosure {Z H : Subgroup G} {g : G}
    (hZ : g ∈ Subgroup.normalizer (Z : Set G)) (hH : g ∈ Subgroup.normalizer (H : Set G)) {x : G}
    (hx : x ∈ conjClosure Z H) : g * x * g⁻¹ ∈ conjClosure Z H := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    have hy' : g * y * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hH y).1 hy
    have hz' : g * z * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 hZ z).1 hz
    have := mem_conjClosure hy' hz'
    simpa [mul_assoc] using this
  | one => simp
  | mul x y _ _ ihx ihy => simpa [mul_assoc] using (conjClosure Z H).mul_mem ihx ihy
  | inv x _ ih => simpa [mul_assoc] using (conjClosure Z H).inv_mem ih

theorem mem_normalizer_conjClosure {Z H : Subgroup G} {g : G}
    (hZ : g ∈ Subgroup.normalizer (Z : Set G)) (hH : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure Z H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_conjClosure hZ hH hx, fun hx => ?_⟩
  have := conj_mem_conjClosure (Subgroup.inv_mem _ hZ) (Subgroup.inv_mem _ hH) hx
  simpa [mul_assoc] using this

theorem lemma97Ab_key {m p : ℕ} (hS : GLStanding G m p) {M D X W : Subgroup G}
    (hD : Prop95Hyp p M D) (h : Lemma97Chief p M D X W) {V : Subgroup G} (hU : IsElemAbelian 2 V)
    {d x : G} (hdp : d ^ p = 1) (hdY : d ∈ Subgroup.normalizer (yGrp D W : Set G))
    (hdV : d ∈ Subgroup.normalizer (V : Set G))
    (hxd : x ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set G)))
    (hxY : x ∈ Subgroup.normalizer (yGrp D W : Set G))
    (hxV : x ∈ Subgroup.normalizer (V : Set G))
    {y : MulAut (IntMod V hU)} (hy : y ∈ autI hU (thompsonJ (yGrp D W)))
    (hδy : convI hU ⟨d, hdV⟩ * y * (convI hU ⟨d, hdV⟩)⁻¹ = y) :
    ∃ k : ℕ, (convI hU ⟨x, hxV⟩ * y * (convI hU ⟨x, hxV⟩)⁻¹ * y⁻¹) ^ (2 ^ k) = 1 := by
  classical
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u', hu'J, rfl⟩ := (mem_autI hU).1 hy
  have huY : (u' : G) ∈ yGrp D W := thompsonJ_le_self _ hu'J
  have huV : (u' : G) ∈ Subgroup.normalizer (V : Set G) := u'.2
  have h1 : d * (u' : G) * d⁻¹ * (u' : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    have h2 : convI hU (⟨d, hdV⟩ * u' * ⟨d, hdV⟩⁻¹ * u'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hδy]
      exact mul_inv_cancel _
    have := (convI_eq_one_iff hU _).1 h2
    simpa using this
  have hKY : d * (u' : G) * d⁻¹ * (u' : G)⁻¹ ∈ yGrp D W ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨?_, h1⟩
    have := (Subgroup.mem_normalizer_iff.1 hdY (u' : G)).1 huY
    exact (yGrp D W).mul_mem this ((yGrp D W).inv_mem huY)
  have hcenV : Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    B2F.normalizer_le_normalizer_centralizer V
  have hdK : d ∈ Subgroup.normalizer ((yGrp D W ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
      Set G) := mem_normalizer_inf hdY (hcenV hdV)
  have huK : (u' : G) ∈ Subgroup.normalizer ((yGrp D W ⊓ Subgroup.centralizer (V : Set G) :
      Subgroup G) : Set G) := mem_normalizer_inf (Subgroup.le_normalizer huY) (hcenV huV)
  have hdpg : IsPGroup p (Subgroup.zpowers d) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]
  have hVp : ¬ p ∣ Nat.card ↥(yGrp D W ⊓ Subgroup.centralizer (V : Set G)) := fun hdvd =>
    not_dvd_card_yGrp hS hD h (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨v, hvK, huvC⟩ := exists_mul_mem_centralizer hdpg hVp hdK huK hKY
  have hvV : v ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer (V : Set G) hvK.2
  have hwY : (u' : G) * v ∈ yGrp D W := (yGrp D W).mul_mem huY hvK.1
  have hwV : (u' : G) * v ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ huV hvV
  set z : G := x * ((u' : G) * v) * x⁻¹ * ((u' : G) * v)⁻¹ with hz
  have hzH : z ∈ pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) := by
    have hw := le_normalizer_pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) huvC
    have := (Subgroup.mem_normalizer_iff.1 hw x⁻¹).1 ((pCoreOf 2 _).inv_mem hxd)
    have := (pCoreOf 2 (Subgroup.centralizer ({d} : Set G))).mul_mem hxd this
    simpa [hz, mul_assoc] using this
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.centralizer ({d} : Set G))
    ⟨z, hzH⟩
  have hzk : z ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨k, ?_⟩
  have hρv : convI hU ⟨v, hvV⟩ = 1 := (convI_eq_one_iff hU _).2 hvK.2
  have hρw : convI hU (⟨(u' : G) * v, hwV⟩ : ↥(Subgroup.normalizer (V : Set G))) = convI hU u' := by
    have : (⟨(u' : G) * v, hwV⟩ : ↥(Subgroup.normalizer (V : Set G))) = u' * ⟨v, hvV⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, hρv, mul_one]
  rw [← hρw]
  have h3 : convI hU ⟨x, hxV⟩ * convI hU ⟨(u' : G) * v, hwV⟩ * (convI hU ⟨x, hxV⟩)⁻¹ *
      (convI hU ⟨(u' : G) * v, hwV⟩)⁻¹ =
      convI hU (⟨x, hxV⟩ * ⟨(u' : G) * v, hwV⟩ * ⟨x, hxV⟩⁻¹ * ⟨(u' : G) * v, hwV⟩⁻¹) := by
    simp only [map_mul, map_inv]
  rw [h3, ← map_pow]
  have h4 : (⟨x, hxV⟩ * ⟨(u' : G) * v, hwV⟩ * ⟨x, hxV⟩⁻¹ * ⟨(u' : G) * v, hwV⟩⁻¹ :
      ↥(Subgroup.normalizer (V : Set G))) ^ (2 ^ k) = 1 := by
    refine Subtype.ext ?_
    simpa [hz] using hzk
  rw [h4, map_one]

theorem lemma97Ab_case2 {m p : ℕ} (hS : GLStanding G m p) {M D X W : Subgroup G}
    (hD : Prop95Hyp p M D) (h : Lemma97Chief p M D X W) (hab : ⁅W, W⁆ ≤ X)
    {V : Subgroup G} (hV : V = conjClosure (quasithinOmegaOneCenter (gammaD D)) (yGrp D W))
    (hU : IsElemAbelian 2 V)
    (hJ : ¬ thompsonJ (gammaD D) ≤ Subgroup.centralizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))}
    (hSyl : IsSylowTwoOf (autI hU (thompsonJ (gammaD D))) (autI hU (thompsonJ (yGrp D W))))
    (hJeq : autI hU (thompsonJ (yGrp D W)) = ⨆ L ∈ I, L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (hnat : ∀ L ∈ I, ActsAsNaturalL2 L (commV L)) : False := by
  classical
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hΓM : gammaD D ≤ M := gammaD_le_of_hyp hD
  have hYM : yGrp D W ≤ M := yGrp_le_M hD h
  have hΓY : gammaD D ≤ yGrp D W := gammaD_le_yGrp
  have hYN : ∀ g ∈ M, g ∈ Subgroup.normalizer (gammaD D : Set G) →
      g ∈ Subgroup.normalizer (yGrp D W : Set G) := fun g hg hg' => mem_normalizer_yGrp hD h hg hg'
  have hVN : ∀ g ∈ M, g ∈ Subgroup.normalizer (gammaD D : Set G) →
      g ∈ Subgroup.normalizer (V : Set G) := by
    intro g hgM hgΓ
    subst hV
    exact mem_normalizer_conjClosure ((isCharIn_omegaOneCenter _).normalizer_le hgΓ) (hYN g hgM hgΓ)
  have hYV : yGrp D W ≤ Subgroup.normalizer (V : Set G) := by
    intro y hy
    subst hV
    exact le_normalizer_conjClosure _ _ hy
  have hSigM : sigmaStar D ≤ M := sigmaStar_le_of_hyp hD
  have hSigN : sigmaStar D ≤ Subgroup.normalizer (gammaD D : Set G) :=
    sigmaStar_le_normalizer_gammaD D
  have hDN : D ≤ Subgroup.normalizer (gammaD D : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_gammaD D)
  have hI : IsSigma3Family I :=
    ⟨hcomm, hind, fun L hL => by obtain ⟨e, _⟩ := hnat L hL; exact ⟨e⟩⟩
  have hJρ : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)),
      g ∈ Subgroup.normalizer (yGrp D W : Set G) →
      convI hU ⟨g, hg⟩ ∈ Subgroup.normalizer
        ((⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))) : Set (MulAut (IntMod V hU))) := by
    intro g hg hgY
    rw [← hJeq, Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe,
      autI_cjSub hU hg, cjSub_thompsonJ hgY]
  have hYsyl := isSylowTwoOf_gammaD_yGrp hD h hab
  set E : Set (MulAut (IntMod V hU)) :=
    {e | e ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))) ∧ e ^ 3 = 1} with hE
  set C : Subgroup G :=
    ((Subgroup.centralizer E).comap (convI hU)).map (Subgroup.normalizer (V : Set G)).subtype
    with hC
  have hHd : ∀ d ∈ D, d ≠ 1 → pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ≤ C := by
    intro d hd hd1 x hx
    have hxS : x ∈ sigmaStar D :=
      (le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le hd1 le_rfl)) : pCoreOf 2
        (Subgroup.centralizer ({d} : Set G)) ≤ sigmaStar D) hx
    have hxM : x ∈ M := hSigM hxS
    have hxΓ := hSigN hxS
    have hxV := hVN x hxM hxΓ
    have hxY := hYN x hxM hxΓ
    have hdM : d ∈ M := hD.le hd
    have hdΓ := hDN hd
    have hdV := hVN d hdM hdΓ
    have hdY := hYN d hdM hdΓ
    have hdp : d ^ p = 1 := hD.plane.1.2 d hd
    have hδp : (convI hU ⟨d, hdV⟩) ^ p = 1 := by
      rw [← map_pow]
      have : (⟨d, hdV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ p = 1 :=
        Subtype.ext (by simpa using hdp)
      rw [this, map_one]
    obtain ⟨m', hm'⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer ({d} : Set G)) ⟨x, hx⟩
    have hhm : (convI hU ⟨x, hxV⟩) ^ (2 ^ m') = 1 := by
      rw [← map_pow]
      have : (⟨x, hxV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ (2 ^ m') = 1 := by
        refine Subtype.ext ?_
        have := congrArg Subtype.val hm'
        simpa using this
      rw [this, map_one]
    have hxC : x ∈ Subgroup.centralizer ({d} : Set G) :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
    have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.1 hxC
    have hδh : convI hU ⟨d, hdV⟩ * convI hU ⟨x, hxV⟩ = convI hU ⟨x, hxV⟩ * convI hU ⟨d, hdV⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hxd.symm)
    have key : ∀ y ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))),
        convI hU ⟨d, hdV⟩ * y * (convI hU ⟨d, hdV⟩)⁻¹ = y →
        ∃ k : ℕ, (convI hU ⟨x, hxV⟩ * y * (convI hU ⟨x, hxV⟩)⁻¹ * y⁻¹) ^ (2 ^ k) = 1 :=
      fun y hy hδy => lemma97Ab_key hS hD h hU hdp hdY hdV hx hxY hxV
        (by rw [hJeq]; exact hy) hδy
    have hmain := hI.main hp hp2 (hJρ d hdV hdY) (hJρ x hxV hxY) hδp hhm hδh key
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    show convI hU ⟨x, hxV⟩ ∈ Subgroup.centralizer E
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have := hmain e he.1 he.2
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  have hSC : sigmaStar D ≤ C :=
    iSup_le fun d => iSup_le fun hd => iSup_le fun hd1 => hHd d hd hd1
  have hJV : thompsonJ (gammaD D) ≤ Subgroup.normalizer (V : Set G) :=
    (thompsonJ_le_self _).trans (hΓY.trans hYV)
  have hS0 : autI hU (thompsonJ (gammaD D)) ≠ ⊥ := fun hbot => hJ ((autI_eq_bot_iff hU hJV).1 hbot)
  obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hS0
  have hsmem : (s : MulAut (IntMod V hU)) ∈ autI hU (thompsonJ (gammaD D)) := s.2
  obtain ⟨g', hgJ, hgs⟩ := (mem_autI hU).1 hsmem
  have hgC : (g' : G) ∈ C := hSC (gammaD_le_sigmaStar D (thompsonJ_le_self _ hgJ))
  obtain ⟨g'', hg''C, hg''⟩ := hgC
  have hg''eq : g'' = g' := Subtype.ext hg''
  have hsJ : (s : MulAut (IntMod V hU)) ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))) := by
    rw [← hJeq]
    exact autI_mono hU (thompsonJ_le_thompsonJ_of_isSylowTwoOf hYsyl) hsmem
  obtain ⟨k, hk⟩ := hSyl.2.1 s
  have hsk : (s : MulAut (IntMod V hU)) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hsone := hI.eq_one_of_two_pow_of_centralizes hsJ hsk (fun e he he3 => by
    have h1 : e * convI hU g'' = convI hU g'' * e := (Subgroup.mem_centralizer_iff.1 hg''C) e ⟨he, he3⟩
    rw [hg''eq, hgs] at h1
    exact mul_inv_eq_iff_eq_mul.2 h1.symm)
  exact hs1 (Subtype.ext hsone)

end L97

open L97

theorem lemma97Ab_holds : Lemma97Ab := by
  intro G _ _ m p hS M D hD X W h hab
  have hΓM : gammaD D ≤ M := gammaD_le_of_hyp hD
  have hYM : yGrp D W ≤ M := yGrp_le_M hD h
  have hYsyl := isSylowTwoOf_gammaD_yGrp hD h hab
  have hYsolv := isSolvable_yGrp hD h hab
  have hYchar := charTwo_yGrp hS hD h
  have hΓ0 : gammaD D ≠ ⊥ := by
    intro hbot
    obtain ⟨P, hP, hP2, hPO⟩ := exists_ne_bot_le_pCoreOf hD.twoLocal
    exact hP (le_bot_iff.1 ((hPO.trans hD.clause_c).trans hbot.le))
  obtain ⟨hU, hred, hcases, -⟩ := B2_16 hYsolv hYchar hYsyl
    (V := conjClosure (quasithinOmegaOneCenter (gammaD D)) (yGrp D W)) rfl
  rcases hcases with ⟨hJ, hfac⟩ | ⟨hJ, I, hSyl, hJeq, hcomm, hind, hnat, -, -, -, hperm⟩
  ·
    have hnorm := le_normalizer_of_factorization hYsyl
      (gammaD_le_pCoreOf_normalizer_of_isCharIn_gammaD (thompsonJ_ne_bot (isPGroup_gammaD D) hΓ0)
        (isCharIn_thompsonJ _))
      (gammaD_le_pCoreOf_normalizer_of_isCharIn_gammaD
        (omegaOneCenter_ne_bot (isPGroup_gammaD D) hΓ0) (isCharIn_omegaOneCenter _)) hfac
    exact lemma97_false_of_commutator_le_normalizer hD h hab
      (fun x hx => hnorm (commutator_le_yGrp hx))
  · exact lemma97Ab_case2 hS hD h hab rfl hU hJ hSyl hJeq hcomm hind hnat

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
