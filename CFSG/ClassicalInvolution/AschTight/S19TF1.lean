module

public import CFSG.ClassicalInvolution.AschTight.S19TSq
public import CFSG.ClassicalInvolution.AschTight.S19TBr2
public import CFSG.ClassicalInvolution.AschTight.S19LExact
public import CFSG.ClassicalInvolution.AschTight.S19QAct
public import CFSG.ClassicalInvolution.AschTight.S19QSec2
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19FFactM1
public import CFSG.ClassicalInvolution.Asc77.AscIH8Small
public import CFSG.ClassicalInvolution.AschTight.S1911Case2c
public import CFSG.ClassicalInvolution.AschTight.S1916Coh2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q (secY secE secFam secK)

section Gen

theorem mul_conj_mul_inv {E : Type} [Group E] (φ : MulAut E) (e : E) :
    φ * MulAut.conj e * φ⁻¹ = MulAut.conj (φ e) := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]

theorem orderOf_eq_four {E : Type} [Group E] {w s : E} (hww : w * w = s) (hs1 : s ≠ 1)
    (hs2 : s * s = 1) : orderOf w = 4 := by
  have h1 : ¬ w ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, hww]
    exact hs1
  have h2 : w ^ 2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two w, hww, pow_two s, hs2]
  rw [orderOf_eq_prime_pow h1 h2]
  norm_num

variable {Y₀ : Type} [Group Y₀] {Y₁ : Subgroup Y₀} [Y₁.Normal]

theorem residual_of_secAct_eq_conj {s : Y₀} {y : ↥Y₁}
    (h : S1911.secAct Y₁ s = MulAut.conj (QuotientGroup.mk y)) :
    ∀ w ∈ Y₁, (s * (y : Y₀)⁻¹) * w * (s * (y : Y₀)⁻¹)⁻¹ * w⁻¹ ∈ oddCoreOf Y₁ := by
  intro w hw
  have h1 : S1911.secAct Y₁ (s * (y : Y₀)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, S1911.secAct_of_mem Y₁ y.2, mul_inv_cancel]
  have h2 : S1911.secAct Y₁ (s * (y : Y₀)⁻¹) (QuotientGroup.mk ⟨w, hw⟩) =
      QuotientGroup.mk ⟨w, hw⟩ := by
    rw [h1]
    rfl
  have h3 := S19Q.conj_mem_oddCoreOf hw (S1911.mem_oddCoreOf_of_secAct hw h2)
  convert h3 using 1
  group

end Gen

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem mul_t_mem_centralizer (hd : Sec19DataT p f K z S W L t V) {u : G} (huU : u ∈ K ⊓ W)
    (huu : u * u = z) :
    u * t ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hd0 := hd.toSec19Data
  have hcomm := S1911.comm_of_mem hd0
  have htW := S1911.mem_W hd
  have hzW : z ∈ W := (S1916.isUniqueInvolution_W_inf hd).mem.1
  have hzt : z * t = t * z := hcomm z hzW t htW
  have hut : u * t = t * u := hcomm u huU.2 t htW
  obtain ⟨r₀, hr₀, hr₀t⟩ := S1911.exists_conj_eq_mul hd
  have hr₀u := S1911.conj_eq_inv_of_conj_eq_mul hd hr₀ hr₀t u huU
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hrz : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hd0.hSz hr.1)
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := S19B.le_normalizer_W hd hr.1
  have hrtW : r * t * r⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hrN t).mp htW
  have hrt2 : r * t * r⁻¹ * (r * t * r⁻¹) = 1 := by
    calc r * t * r⁻¹ * (r * t * r⁻¹) = r * (t * t) * r⁻¹ := by group
      _ = 1 := by rw [hd.invL.sq]; group
  have hrt1 : r * t * r⁻¹ ≠ 1 := by
    intro h
    apply hd.invL.ne_one
    calc t = r⁻¹ * (r * t * r⁻¹) * r := by group
      _ = 1 := by rw [h]; group
  have key : r * u * r⁻¹ * (r * t * r⁻¹) = u * t := by
    rcases S1911.invol_mem_W hd hrtW hrt2 hrt1 with h | h | h
    · exfalso
      apply hd.ne
      calc t = r⁻¹ * (r * t * r⁻¹) * r := by group
        _ = z := by rw [h, mul_assoc, ← hrz, inv_mul_cancel_left]
    · have hrr₀ : r * r₀ * t * (r * r₀)⁻¹ = t * z := by
        calc r * r₀ * t * (r * r₀)⁻¹ = r * (r₀ * t * r₀⁻¹) * r⁻¹ := by group
          _ = r * t * r⁻¹ * (r * z * r⁻¹) := by rw [hr₀t]; group
          _ = t * z := by rw [h, hrz, mul_inv_cancel_right]
      have h1 := S1911.conj_eq_inv_of_conj_eq_mul hd (Subgroup.mul_mem _ hr hr₀) hrr₀ u huU
      have h2 : r₀⁻¹ * u * r₀ = u⁻¹ := by
        calc r₀⁻¹ * u * r₀ = (r₀⁻¹ * u⁻¹ * r₀)⁻¹ := by group
          _ = (r₀⁻¹ * (r₀ * u * r₀⁻¹) * r₀)⁻¹ := by rw [hr₀u]
          _ = u⁻¹ := by group
      have h3 : r * u * r⁻¹ = u := by
        calc r * u * r⁻¹ = (r * r₀) * (r₀⁻¹ * u * r₀) * (r * r₀)⁻¹ := by group
          _ = ((r * r₀) * u * (r * r₀)⁻¹)⁻¹ := by rw [h2]; group
          _ = u := by rw [h1, inv_inv]
      rw [h3, h]
    · have h1 := S1911.conj_eq_inv_of_conj_eq_mul hd hr h u huU
      rw [h1, h]
      calc u⁻¹ * (t * z) = u⁻¹ * (z * t) := by rw [hzt]
        _ = u⁻¹ * (u * u) * t := by rw [huu]; group
        _ = u * t := by group
  calc r * (u * t) = (r * u * r⁻¹ * (r * t * r⁻¹)) * r := by group
    _ = u * t * r := by rw [key]

theorem exists_conj_of_mem_S (hFL : FactFL) (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) (hzx : z ∈ Subgroup.centralizer ({x} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({x} : Set G)))
    [IsSimpleGroup (secE K x)] {tg : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e' : ℕ}
    (M : Ih8Model p f (secFam K x) tg k e') (htg : (tg = .PSL ∧ k = 3) ∨ (tg = .PSU ∧ k = 3))
    (hO : oddCoreOf (secK K x) = ⊥) (s : ↥(Subgroup.centralizer ({x} : Set G)))
    (hsS : (s : G) ∈ (S : Subgroup G)) {g : G} (hsg : (s : G) = g * z * g⁻¹)
    (hsz : (s : G) * z = z * (s : G)) :
    ∃ e : secE K x, S1911.secAct (secY K x) s = MulAut.conj e := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hp2 := hd.tight.branch.odd
  have h5 := hd.tight.branch.five
  have hcomm := S1911.comm_of_mem hd0
  have htW := S1911.mem_W hd
  have hzW : z ∈ W := (S1916.isUniqueInvolution_W_inf hd).mem.1
  have hxS : x ∈ (S : Subgroup G) := hx.1.1.1
  have hxW := hx.1.2
  have hsx : (s : G) * x = x * (s : G) := Subgroup.mem_centralizer_singleton_iff.mp s.2
  have hLY : S1911.perfectCoreIn K x ≤ secY K x := S1911.le_conjGen ⟨1, conjSub_one _⟩
  have hzY : ∀ h : ↥(Subgroup.centralizer ({x} : Set G)), h * ⟨z, hzx⟩ * h⁻¹ ∈ secY K x :=
    fun h => S1911.le_conjGen ⟨h, rfl⟩
      (S1911.isUniqueInvolution_conjSub_perfectCoreIn hd0 hzx hzKa h).mem
  have hinner : (∃ h ∈ Subgroup.centralizer ({x} : Set G), h * z * h⁻¹ = (s : G)) →
      ∃ e : secE K x, S1911.secAct (secY K x) s = MulAut.conj e := by
    rintro ⟨h, hh, he⟩
    have hsY : s ∈ secY K x := by
      have e : s = ⟨h, hh⟩ * ⟨z, hzx⟩ * ⟨h, hh⟩⁻¹ := Subtype.ext (by simp [he])
      rw [e]
      exact hzY _
    exact ⟨_, S1911.secAct_of_mem _ hsY⟩
  have hs2 : (s : G) * (s : G) = 1 := by
    rw [hsg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  have hsN : (s : G) ∈ Subgroup.normalizer (W : Set G) := S19B.le_normalizer_W hd hsS
  have hstW : (s : G) * t * (s : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hsN t).mp htW
  have hst2 : (s : G) * t * (s : G)⁻¹ * ((s : G) * t * (s : G)⁻¹) = 1 := by
    calc (s : G) * t * (s : G)⁻¹ * ((s : G) * t * (s : G)⁻¹) = (s : G) * (t * t) * (s : G)⁻¹ := by
          group
      _ = 1 := by rw [hd.invL.sq]; group
  have hst1 : (s : G) * t * (s : G)⁻¹ ≠ 1 := by
    intro h
    apply hd.invL.ne_one
    calc t = (s : G)⁻¹ * ((s : G) * t * (s : G)⁻¹) * (s : G) := by group
      _ = 1 := by rw [h]; group
  rcases S1911.invol_mem_W hd hstW hst2 hst1 with h | h | h
  · exfalso
    apply hd.ne
    calc t = (s : G)⁻¹ * ((s : G) * t * (s : G)⁻¹) * (s : G) := by group
      _ = z := by rw [h, mul_assoc, ← hsz, inv_mul_cancel_left]
  ·
    apply hinner
    have hst : (s : G) * t = t * (s : G) := by
      calc (s : G) * t = (s : G) * t * (s : G)⁻¹ * (s : G) := by group
        _ = t * (s : G) := by rw [h]
    rw [hsg] at hsx hsz hst ⊢
    exact exists_conj_eq_of_comm_t hd hx hsx hsz hst
  have hsne : (s : G) ≠ z := by
    intro he
    rw [he] at h
    have h1 : z * t * z⁻¹ = t := by rw [hcomm z hzW t htW, mul_inv_cancel_right]
    rw [h1] at h
    exact hI.ne_one (mul_left_cancel (a := t) (by rw [mul_one]; exact h.symm))
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := S1911.exists_eta hd0
  have hU : K ⊓ W ∈ USet (CoreAssembly.conjClass K) :=
    (hη.1 (S1911.inf_mem_eta hd0 hη hinv hWη hηS)).1
  obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ :=
    (hypOmegaMod_of_tightD hd.tight).exists_data_of_mem_USet hp2 hU
  obtain ⟨u, huU, huu⟩ := exists_mul_self_eq_of_isCyclic hI inf_le_left hcyc
    (S.isPGroup'.to_le (inf_le_right.trans hd.hWS)) h4
  have hzU : IsUniqueInvolution (K ⊓ W) z :=
    ⟨⟨hI.mem, hzW⟩, hI.ne_one, hI.sq, fun y hy hy2 => hI.unique y hy.1 hy2⟩
  have hsK : (s : G) ∈ Subgroup.normalizer (K : Set G) :=
    S1911.centralizer_le_normalizer_member htb (CoreAssembly.mem_conjClass_self K) hI
      (Subgroup.mem_centralizer_singleton_iff.mpr hsz)
  have hsuU : (s : G) * u * (s : G)⁻¹ ∈ K ⊓ W :=
    ⟨(Subgroup.mem_normalizer_iff.mp hsK u).mp huU.1,
      (Subgroup.mem_normalizer_iff.mp hsN u).mp huU.2⟩
  have hszs : (s : G) * z * (s : G)⁻¹ = z := by rw [hsz, mul_inv_cancel_right]
  have hsuu : (s : G) * u * (s : G)⁻¹ * ((s : G) * u * (s : G)⁻¹) = z := by
    calc (s : G) * u * (s : G)⁻¹ * ((s : G) * u * (s : G)⁻¹) = (s : G) * (u * u) * (s : G)⁻¹ := by
          group
      _ = z := by rw [huu, hszs]
  rcases S1916.eq_or_eq_inv_of_mul_self_eq hzU (fun a ha b hb => hcomm a ha.2 b hb.2) hsuU huU
    hsuu huu with h' | h'
  ·
    apply hinner
    have hus : u * (s : G) = (s : G) * u := by
      calc u * (s : G) = (s : G) * u * (s : G)⁻¹ * (s : G) := by rw [h']
        _ = (s : G) * u := by group
    rw [hsg] at hsx hsne hus ⊢
    exact exists_conj_eq_of_comm_u hd hx hsx hsne huU.1 (orderOf_eq_four huu hI.ne_one hI.sq) hus
  have hux : u * x = x * u := Subgroup.mem_centralizer_iff.mp hxW u huU.2
  have htx : t * x = x * t := Subgroup.mem_centralizer_iff.mp hxW t htW
  have hut : u * t = t * u := hcomm u huU.2 t htW
  have hζx : u * t ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * t * x = u * (t * x) := by group
      _ = (u * x) * t := by rw [htx]; group
      _ = x * (u * t) := by rw [hux]; group
  have hζS : u * t ∈ (S : Subgroup G) := Subgroup.mul_mem _ (hd.hWS huU.2) (hd.hWS htW)
  have hζK : u * t ∈ centralizerModOdd ⊤ K :=
    S19B.mem_centralizerModOdd_K hd hζS (mul_t_mem_centralizer hd huU huu)
  have hζz : u * t * z = z * (u * t) := hcomm _ (W.mul_mem huU.2 htW) z hzW
  have hζs : (s : G) * (u * t) * (s : G)⁻¹ = u * t := by
    calc (s : G) * (u * t) * (s : G)⁻¹ =
          ((s : G) * u * (s : G)⁻¹) * ((s : G) * t * (s : G)⁻¹) := by group
      _ = u⁻¹ * (z * t) := by rw [h', h, hcomm t htW z hzW]
      _ = u⁻¹ * (u * u) * t := by rw [huu]; group
      _ = u * t := by group
  have hζζ : u * t * (u * t) = z := by
    calc u * t * (u * t) = u * (t * u) * t := by group
      _ = u * u * (t * t) := by rw [← hut]; group
      _ = z := by rw [huu, hd.invL.sq, mul_one]
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)
  have hxK : x ∈ centralizerModOdd ⊤ K := S19B.mem_centralizerModOdd_K hd hxS hx.1.1.2
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hd.hWS huU.2))
  have huKx := mem_perfectResidualOf_of_cStar hd0 hx2 hxK huU.1
    (Subgroup.mem_centralizer_singleton_iff.mpr hux) hu2
  have huY : (⟨u, Subgroup.mem_centralizer_singleton_iff.mpr hux⟩ :
      ↥(Subgroup.centralizer ({x} : Set G))) ∈ secY K x :=
    hLY (Subgroup.mem_subgroupOf.mpr huKx)
  obtain ⟨h₁, hh₁, he₁⟩ := exists_conj_eq_t hd hx
  have htY : (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr htx⟩ :
      ↥(Subgroup.centralizer ({x} : Set G))) ∈ secY K x := by
    have e : (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr htx⟩ :
        ↥(Subgroup.centralizer ({x} : Set G))) = ⟨h₁, hh₁⟩ * ⟨z, hzx⟩ * ⟨h₁, hh₁⟩⁻¹ :=
      Subtype.ext (by simp [he₁])
    rw [e]
    exact hzY _
  have hζY : (⟨u * t, hζx⟩ : ↥(Subgroup.centralizer ({x} : Set G))) ∈ secY K x :=
    Subgroup.mul_mem _ huY htY
  set c : secE K x := QuotientGroup.mk ⟨⟨u * t, hζx⟩, hζY⟩ with hc
  have hKΦ : secK K x ∈ secFam K x :=
    (S1911.mem_secFamily_iff (S1911.perfectCoreIn K x) (secK K x)).mpr ⟨1, by rw [conjSub_one]⟩
  have hφ2 : S1911.secAct (secY K x) s * S1911.secAct (secY K x) s = 1 := by
    rw [← map_mul, show s * s = 1 from Subtype.ext hs2, map_one]
  have hφL : (secK K x).map (S1911.secAct (secY K x) s).toMonoidHom = secK K x := by
    rw [S1911.secAct_secImg _ s hLY,
      conjSub_eq_of_mem_normalizer (S1911.mem_normalizer_perfectCoreIn hd0 hsz)]
  have hab : ∀ P : Subgroup (secE K x), IsPGroup 2 P → P ≤ secK K x →
      (∀ y ∈ P, S1911.secAct (secY K x) s y = y) → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro P hP2 hPL hfix a ha b hb
    by_contra hne
    exact S1911.false_of_fixes_nonabelian hd0 ⟨g, hsg⟩ hsz (Subtype.ext hs2) hsne hP2 hPL hfix
      ⟨a, ha, b, hb, hne⟩
  have hcC : c ∈ Subgroup.centralizer ((secK K x : Subgroup (secE K x)) : Set (secE K x)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hfix := S19Q.secAct_fixes_of_mem_cStar hd0 hO (y := ⟨u * t, hζx⟩) hζz hζK y hy
    rw [S1911.secAct_of_mem _ hζY, MulAut.conj_apply] at hfix
    calc y * c = c * y * c⁻¹ * c := by rw [hfix]
      _ = c * y := by group
  have hcφ : S1911.secAct (secY K x) s c = c := by
    rw [hc, S1911.secAct_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hζs
  have hcc : c * c ≠ 1 := by
    intro h1
    rw [hc, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at h1
    apply (S1911.isUniqueInvolution_secImg hd0 hzx hzKa 1).ne_one
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    convert h1 using 1
    apply Subtype.ext
    apply Subtype.ext
    simp [hζζ]
  exact exists_conj_of_fixes hFL hp2 h5 htg M hKΦ _ hφ2 hφL hab ⟨c, hcC, hcφ, hcc⟩

theorem residual_of_FL (hFL : FactFL) (hd : Sec19DataT p f K z S W L t V) {x : G}
    (hx : x ∈ S19B.sec19BPrime K S W L) (hx1 : x ≠ 1) :
    (SectionLieType p f (S1911.conjFamily (S1911.perfectCoreIn K x))
        (S1911.conjGen (S1911.perfectCoreIn K x)) .PSL 3 ∨
      SectionLieType p f (S1911.conjFamily (S1911.perfectCoreIn K x))
        (S1911.conjGen (S1911.perfectCoreIn K x)) .PSU 3) →
      ∀ s : ↥(Subgroup.centralizer ({x} : Set G)), (∃ g : G, (s : G) = g * z * g⁻¹) →
        (s : G) * z = z * (s : G) →
        ∃ y ∈ S1911.conjGen (S1911.perfectCoreIn K x),
          ∀ w ∈ S1911.conjGen (S1911.perfectCoreIn K x),
            (s * y⁻¹) * w * (s * y⁻¹)⁻¹ * w⁻¹ ∈
              oddCoreOf (S1911.conjGen (S1911.perfectCoreIn K x)) := by
  intro hsec s hs hsz
  obtain ⟨g, hsg⟩ := hs
  obtain ⟨hzx, hmem, hΩ, hDE, -, -⟩ := S19Q.section_inputs_of_mem_sec19BPrime hd hx hx1
  have hd0 := hd.toSec19Data
  have hp2 := hd.tight.branch.odd
  have h5 := hd.tight.branch.five
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hmem.mem
  have hconj := conjInvariant_oddQuotientFamily
    (S1911.inClass_restrict_conjugates hmem).conjInvariant
  obtain ⟨tg, htg, D, hcard, i, hti, hki⟩ : ∃ tg : CFSG.Assembly.LowTwoRank.StatedLieTag,
      (tg = .PSL ∨ tg = .PSU) ∧ SectionLieType p f (S1911.conjFamily (S1911.perfectCoreIn K x))
        (S1911.conjGen (S1911.perfectCoreIn K x)) tg 3 := by
    rcases hsec with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have htg' : (D.tag i = .PSL ∧ D.rank i = 3) ∨ (D.tag i = .PSU ∧ D.rank i = 3) := by
    rw [hti, hki]
    rcases htg with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have htag : S1911.IsT6Tag (D.tag i) (D.rank i) := by
    rcases htg' with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hO' := CFSG.ComponentClassification.OddCore.quotient_corefree
    ↥(S1911.conjGen (S1911.perfectCoreIn K x))
  have hu1 := S1911.isUniqueInvolution_secImg hd0 hzx hzKa 1
  have : Nontrivial (secE K x) := ⟨⟨_, 1, hu1.ne_one⟩⟩
  have := S1911.isSimpleGroup_of_lieSystemData S19M.factM3 hp2 D hcard i htag hO'
  have M := S1911.ih8Model_of_lieSystemData D hcard i hconj
  have hO := (S19L.secK_exact hd0 h5 hΩ hDE M (htg'.imp (·.1) (·.1))).1
  have hs2 : (s : G) * (s : G) = 1 := by
    rw [hsg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  have hs2' : IsPGroup 2 (Subgroup.zpowers (s : G)) :=
    (isPGroup_zpowers_iff _).mpr ⟨1, by rw [pow_one, sq, hs2]⟩
  obtain ⟨S', hd', hx', c, hc, hcs⟩ := exists_sylow_conj hd hx s.2
    (Subgroup.mem_centralizer_singleton_iff.mpr hsz) hs2'
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  set c' : ↥(Subgroup.centralizer ({x} : Set G)) := ⟨c, hc.1⟩ with hc'
  have hcoe : ((c' * s * c'⁻¹ : ↥(Subgroup.centralizer ({x} : Set G))) : G) =
      c * (s : G) * c⁻¹ := rfl
  have hs'g : ((c' * s * c'⁻¹ : ↥(Subgroup.centralizer ({x} : Set G))) : G) =
      (c * g) * z * (c * g)⁻¹ := by
    rw [hcoe, hsg]
    group
  have hs'z : ((c' * s * c'⁻¹ : ↥(Subgroup.centralizer ({x} : Set G))) : G) * z =
      z * ((c' * s * c'⁻¹ : ↥(Subgroup.centralizer ({x} : Set G))) : G) := by
    rw [hcoe]
    have hcz' : c⁻¹ * z * c = z := by rw [mul_assoc, ← hcz, inv_mul_cancel_left]
    calc c * (s : G) * c⁻¹ * z = c * (s : G) * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = c * ((s : G) * z) * c⁻¹ := by rw [hcz']; group
      _ = c * (z * (s : G)) * c⁻¹ := by rw [hsz]
      _ = (c * z) * (s : G) * c⁻¹ := by group
      _ = z * (c * (s : G) * c⁻¹) := by rw [hcz]; group
  obtain ⟨e, he⟩ := exists_conj_of_mem_S hFL hd' hx' hzx hzKa M htg' hO (c' * s * c'⁻¹)
    (hcoe ▸ hcs) hs'g hs'z
  have hsecs : S1911.secAct (secY K x) s = MulAut.conj (S1911.secAct (secY K x) c'⁻¹ e) := by
    have e1 : s = c'⁻¹ * (c' * s * c'⁻¹) * c' := by group
    rw [e1, map_mul, map_mul, he, ← mul_conj_mul_inv, map_inv, inv_inv]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (S1911.secAct (secY K x) c'⁻¹ e)
  rw [← hy] at hsecs
  exact ⟨y, y.2, residual_of_secAct_eq_conj hsecs⟩

theorem exists_conj_eq_of_mem_sec19BPrime' (hFL : FactFL) (hd : Sec19DataT p f K z S W L t V)
    {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) (hx1 : x ≠ 1) {g : G}
    (hg : g * z * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G)) :
    ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * z * c⁻¹ = g * z * g⁻¹ := by
  obtain ⟨hzx, hmem, hΩ, hDE, hlt, hTop⟩ := S19Q.section_inputs_of_mem_sec19BPrime hd hx hx1
  have hd0 := hd.toSec19Data
  have hp2 : p ≠ 2 := hd0.tight.branch.odd
  have h5 : 5 ≤ p ^ f := hd0.tight.branch.five
  have hsec := sectionThm6 hp2 h5 (ih8SmallEdge p) (hd0.ih f h5) hlt hΩ
    ⟨_, ⟨1, conjSub_one _⟩⟩ hDE hTop
  obtain ⟨c, hc⟩ := S19C.fusion_of_sectionType' S19F.factM1 hd0 h5 hzx hmem hΩ hDE hsec
    (residual_of_FL hFL hd hx hx1) ⟨g * z * g⁻¹, hg⟩ ⟨g, rfl⟩
  exact ⟨c, c.2, (congrArg Subtype.val hc).symm⟩

theorem exists_mem_centralizer_conj_eq' (hFL : FactFL) (hd : Sec19DataT p f K z S W L t V)
    {x : G} (hx : x ∈ S19B.sec19BPrime K S W L) (hx1 : x ≠ 1) {g : G}
    (hgx : g⁻¹ * x * g ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ d ∈ Subgroup.centralizer ({z} : Set G), d⁻¹ * x * d = g⁻¹ * x * g := by
  have hgx' := Subgroup.mem_centralizer_singleton_iff.mp hgx
  have h1 : g * z * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [← hgx']
      _ = x * (g * z * g⁻¹) := by group
  obtain ⟨c, hc, hcz⟩ := exists_conj_eq_of_mem_sec19BPrime' hFL hd hx hx1 h1
  have hcx := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine ⟨c⁻¹ * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * g * z = c⁻¹ * (g * z * g⁻¹) * g := by group
      _ = c⁻¹ * (c * z * c⁻¹) * g := by rw [hcz]
      _ = z * (c⁻¹ * g) := by group
  · calc (c⁻¹ * g)⁻¹ * x * (c⁻¹ * g) = g⁻¹ * (c * x * c⁻¹) * g := by group
      _ = g⁻¹ * x * g := by rw [hcx]; group

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19T
