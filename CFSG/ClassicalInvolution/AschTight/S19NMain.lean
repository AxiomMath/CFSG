module

public import CFSG.ClassicalInvolution.AschTight.S19NW
public import CFSG.ClassicalInvolution.AschTight.S19NSc
public import CFSG.ClassicalInvolution.AschTight.S19B93b
public import CFSG.ClassicalInvolution.AschTight.S19QTMain
public import CFSG.ClassicalInvolution.AschTight.Thm6TightB3
public import CFSG.ClassicalInvolution.AschTight.S1916F16

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_conj_t_of_transfer [IsSimpleGroup G] (hdT : Sec19DataT p f K z S W L t V)
    {g w : G} (hne : g⁻¹ * z * g ≠ z) (hwK : w ∈ K) (hw4 : orderOf w = 4)
    (hwz : g⁻¹ * w * g * z = z * (g⁻¹ * w * g)) :
    ∃ y₀ ∈ sec19X K z, y₀ * t * y₀⁻¹ = g⁻¹ * z * g := by
  have hI := isUniqueInvolution_of_tight hdT.tight.toTightBranch
  have hne' : g * z * g⁻¹ ≠ z := fun h => hne (by
    calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [h]
      _ = z := by group)
  have hcomm : w * (g * z * g⁻¹) = (g * z * g⁻¹) * w := by
    calc w * (g * z * g⁻¹) = g * (g⁻¹ * w * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hwz]
      _ = (g * z * g⁻¹) * w := by group
  obtain ⟨U', hU', hU'C, hzU'⟩ := S19B.exists_mem_USet_of_comm hdT hne' hwK hw4 hcomm
  have h2 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hI.sq]; group
  have h1 : g⁻¹ * z * g ≠ 1 := fun h => hI.ne_one (by
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  exact S19B.exists_conj_t_of_mem_USet hdT hU' hU'C hzU' h2 h1 hne

theorem exists_conj_mem_normalizer [IsSimpleGroup G] (hdT : Sec19DataT p f K z S W L t V)
    {b : G} (hbz : b ∈ Subgroup.centralizer ({z} : Set G))
    (hbt : b ∈ Subgroup.centralizer ({t} : Set G)) (hb2 : IsPGroup 2 (Subgroup.zpowers b)) :
    ∃ h ∈ Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G),
      h⁻¹ * b * h ∈ Subgroup.normalizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hdT.toSec19Data
  have hcomm := S1911.comm_of_mem hd
  have hzW : z ∈ W := (S1916.isUniqueInvolution_W_inf hdT).mem.1
  have htW : t ∈ W := S1911.mem_W hdT
  set H₂ := Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) with hH₂
  have hWH : W ≤ H₂ := fun x hx =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx z hzW),
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx t htW)⟩
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hd.hWS
  obtain ⟨P, hP, hWP⟩ := IsSylow2In.exists_ge hW2 hWH
  have hPN : P ≤ Subgroup.normalizer (W : Set G) := by
    intro x hxP
    refine mem_normalizer_iff_conjSub_eq.mpr
      ((S19B.weaklyClosedIn_W hdT).eq_of_le_of_isPGroup hP.2.1 hWP fun y hy => ?_)
    rw [mem_conjSub_iff] at hy
    have e : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [e]
    exact P.mul_mem (P.mul_mem hxP (hWP hy)) (P.inv_mem hxP)
  have hbH : Subgroup.zpowers b ≤ H₂ := Subgroup.zpowers_le.mpr ⟨hbz, hbt⟩
  obtain ⟨h, hh, hle⟩ := Sec7.exists_conj_le_of_isSylow2In hP hb2 hbH
  have hb : b ∈ conjSub h P := hle (Subgroup.mem_zpowers b)
  exact ⟨h, hh, hPN (mem_conjSub_iff.mp hb)⟩

theorem conj_mem_of_mem [IsSimpleGroup G] (hdT : Sec19DataT p f K z S W L t V) (hq : p ^ f = 9)
    (h8 : 8 ≤ Nat.card ↥(K ⊓ W)) {c : G} (hc : L = conjSub c K) {y : G}
    (hyz : y ∈ Subgroup.centralizer ({z} : Set G)) (hyt : y ∈ Subgroup.centralizer ({t} : Set G))
    (hyW : y ∈ Subgroup.normalizer (W : Set G)) (hy2 : y * y = 1)
    (hyH : y ∈ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    c⁻¹ * y * c ∈ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  have hd := hdT.toSec19Data
  obtain ⟨u, v, n, hu, hv, huo, hvo, -, -, -⟩ := exists_gens hdT
  have h8' : 8 ≤ orderOf u := by
    rw [← Nat.card_zpowers, hu]
    exact h8
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := (S1916.sd_normalizer_eq hd).ge hyz
  have hyu : y * u * y⁻¹ ∈ Subgroup.zpowers u := hu ▸
    ⟨(Subgroup.mem_normalizer_iff.mp hyK u).mp huKW.1,
      (Subgroup.mem_normalizer_iff.mp hyW u).mp huKW.2⟩
  obtain ⟨ε, hε, hyε⟩ := zpow_of_mem hd hyK hy2 hyH huKW.1 huo h8' hyu
  have hyV := (zpow_iff hdT hyz hyt hyW ε).mp (hu ▸ hyε)
  have hyL : y ∈ Subgroup.normalizer ((conjSub c K : Subgroup G) : Set G) :=
    hc ▸ S1911.centralizer_le_normalizer_member hd.tight.toTightBranch hdT.memL hdT.invL hyt
  have hvL : v ∈ conjSub c K := hc ▸ S1911.le_member hdT (hv ▸ Subgroup.mem_zpowers v)
  have h8v : 8 ≤ orderOf v := by
    rw [hvo, ← huo]
    exact h8'
  exact mem_of_zpow_conj hd hq hyL hvL hvo h8v hε (hv ▸ hyV)

theorem false_of_eq_nine [IsSimpleGroup G] (hdT : Sec19DataT p f K z S W L t V) (hq : p ^ f = 9)
    {a : G} (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (haH : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hdT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hCz := hd.hSz
  have hN : ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ x,
      x ∈ sec19X K z ⊔ centralizerModOdd ⊤ K ↔
        c * x * c⁻¹ ∈ sec19X K z ⊔ centralizerModOdd ⊤ K := fun c hc =>
    Subgroup.mem_normalizer_iff.mp (S1916.mem_normalizer_sup_cStar hd hc)
  obtain ⟨u₀, hu₀, hu₀8, -, -⟩ := S19L.exists_gen_conj_eq hdT haS ha2 haH
  have h8 : 8 ≤ Nat.card ↥(K ⊓ W) := by
    rw [← hu₀, Nat.card_zpowers]
    exact hu₀8
  obtain ⟨w, hwSK, hwa, -, hw4⟩ := exists_order_four hdT haS ha2 haH
  have hzS : z ∈ (S : Subgroup G) := hd.hWS (S1916.isUniqueInvolution_W_inf hdT).mem.1
  obtain ⟨g, ⟨hbS, hbH⟩, hgC⟩ := S19Q.exists_conj_mem_of_index_two hd.tight.branch.nonabelian S
    (H := sec19X K z ⊔ centralizerModOdd ⊤ K) (fun s hs x hx => (hN s (hCz hs) x).mp hx.2)
    (fun x hx y hy hxH hyH => inv_mul_mem_of_not_mem hd hq (hCz hx) (hCz hy) hxH hyH)
    haS haH ha2
  have hza : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨hzS, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hCz haS)).symm⟩
  have hwa' : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨hwSK.1, Subgroup.mem_centralizer_singleton_iff.mpr hwa⟩
  have hw'' := hgC w hwa'
  have hne : g⁻¹ * z * g ≠ z := by
    intro h
    have hg : g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * z = g * (g⁻¹ * z * g) := by rw [h]
        _ = z * g := by group
    apply haH
    have h1 := (hN g hg _).mp hbH
    rwa [show g * (g⁻¹ * a * g) * g⁻¹ = a by group] at h1
  have hwz : g⁻¹ * w * g * z = z * (g⁻¹ * w * g) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hCz hw''.1)
  obtain ⟨y₀, hy₀X, hy₀⟩ := exists_conj_t_of_transfer hdT hne hwSK.2 hw4 hwz
  have hy₀z : y₀ ∈ Subgroup.centralizer ({z} : Set G) := S1916.sec19X_le_centralizer K z hy₀X
  have hbz : g⁻¹ * a * g ∈ Subgroup.centralizer ({z} : Set G) := hCz hbS
  have hb'z : y₀⁻¹ * (g⁻¹ * a * g) * y₀ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy₀z) hbz) hy₀z
  have haz := Subgroup.mem_centralizer_singleton_iff.mp (hCz haS)
  have hb't : y₀⁻¹ * (g⁻¹ * a * g) * y₀ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have ht' : t = y₀⁻¹ * (g⁻¹ * z * g) * y₀ := by rw [← hy₀]; group
    rw [ht']
    calc y₀⁻¹ * (g⁻¹ * a * g) * y₀ * (y₀⁻¹ * (g⁻¹ * z * g) * y₀) =
        y₀⁻¹ * g⁻¹ * (a * z) * g * y₀ := by group
      _ = y₀⁻¹ * g⁻¹ * (z * a) * g * y₀ := by rw [haz]
      _ = y₀⁻¹ * (g⁻¹ * z * g) * y₀ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) := by group
  have ha1 : a ≠ 1 := fun h => haH (h ▸ Subgroup.one_mem _)
  have hb'1 : y₀⁻¹ * (g⁻¹ * a * g) * y₀ ≠ 1 := fun h => ha1 (by
    calc a = g * y₀ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) * y₀⁻¹ * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hb'2 : y₀⁻¹ * (g⁻¹ * a * g) * y₀ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) = 1 := by
    calc y₀⁻¹ * (g⁻¹ * a * g) * y₀ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) =
        y₀⁻¹ * g⁻¹ * (a * a) * g * y₀ := by group
      _ = 1 := by rw [ha2]; group
  have hb'P : IsPGroup 2 (Subgroup.zpowers (y₀⁻¹ * (g⁻¹ * a * g) * y₀)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hb'2) hb'1, pow_one])
  obtain ⟨h, ⟨hhz, hht⟩, hhW⟩ := exists_conj_mem_normalizer hdT hb'z hb't hb'P
  have hyz : h⁻¹ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) * h ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhz) hb'z) hhz
  have hyt : h⁻¹ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) * h ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hht) hb't) hht
  have hy2 : h⁻¹ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) * h * (h⁻¹ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) * h) =
      1 := by
    calc h⁻¹ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) * h * (h⁻¹ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) * h) =
        h⁻¹ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀)) * h := by group
      _ = 1 := by rw [hb'2]; group
  have hyH : h⁻¹ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) * h ∈ sec19X K z ⊔ centralizerModOdd ⊤ K := by
    have h1 := (hN (y₀ * h)⁻¹ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hy₀z hhz)) _).mp hbH
    rwa [show (y₀ * h)⁻¹ * (g⁻¹ * a * g) * (y₀ * h)⁻¹⁻¹ =
      h⁻¹ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) * h by group] at h1
  obtain ⟨c, hc⟩ := CoreAssembly.single_class K L hdT.memL
  have hct : c * z * c⁻¹ = t := (hI.conj c).eq (hc ▸ hdT.invL)
  have hmem := conj_mem_of_mem hdT hq h8 hc hyz hyt hhW hy2 hyH
  have hht' : h * t * h⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hht, mul_inv_cancel_right]
  have hez : g * y₀ * h * c * z * (g * y₀ * h * c)⁻¹ = z := by
    calc g * y₀ * h * c * z * (g * y₀ * h * c)⁻¹ =
        g * y₀ * (h * (c * z * c⁻¹) * h⁻¹) * y₀⁻¹ * g⁻¹ := by group
      _ = g * (y₀ * t * y₀⁻¹) * g⁻¹ := by rw [hct, hht']; group
      _ = z := by rw [hy₀]; group
  have he : g * y₀ * h * c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * y₀ * h * c * z = g * y₀ * h * c * z * (g * y₀ * h * c)⁻¹ * (g * y₀ * h * c) := by
          group
      _ = z * (g * y₀ * h * c) := by rw [hez]
  apply haH
  have h1 := (hN _ he _).mp hmem
  rwa [show g * y₀ * h * c * (c⁻¹ * (h⁻¹ * (y₀⁻¹ * (g⁻¹ * a * g) * y₀) * h) * c) *
    (g * y₀ * h * c)⁻¹ = a by group] at h1

theorem le_sup_cStar_of_eq_nine [IsSimpleGroup G] (h11b : C19_11bTmp p f)
    (hSC : S1916.C19_14SCTmp p f) (hB3 : GoldschmidtB3Tmp) (hd : Sec19Data p f K z S W)
    (hq : p ^ f = 9) : (S : Subgroup G) ≤ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  by_contra hS
  obtain ⟨a, haS, ha2, haH⟩ :=
    S1916.exists_involution_of_sec19Data p f h11b hSC hB3 G K z S W hd hS
  obtain ⟨L, t, V, hdT⟩ := exists_sec19DataT hd
  exact false_of_eq_nine hdT hq haS ha2 haH

variable (p f) in
theorem c19_16F9_of (h11b : C19_11bTmp p f) (hSC : S1916.C19_14SCTmp p f)
    (hB3 : GoldschmidtB3Tmp) : C19_16F9Tmp p f :=
  fun _ _ _ _ _ _ _ _ hd hq => le_sup_cStar_of_eq_nine h11b hSC hB3 hd hq

variable (p f) in
theorem c19_16F9_of' (h11b : C19_11bTmp p f) : C19_16F9Tmp p f :=
  c19_16F9_of p f h11b (S1916.c19_14SC_of p f (S1916.c19_14Z_of p f (S19Q.c19_14C_of p f h11b)))
    goldschmidtB3Tmp_holds

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19N
