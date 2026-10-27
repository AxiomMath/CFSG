module

public import CFSG.ClassicalInvolution.AschTight.S1916CSR
public import CFSG.ClassicalInvolution.AschTight.S1916Coh2
public import CFSG.ClassicalInvolution.AschTight.S1916NC2
public import CFSG.ClassicalInvolution.AschTight.S1916Data
public import CFSG.ClassicalInvolution.AschTight.Hall196QD
public import CFSG.ClassicalInvolution.AschTight.S1911Case2c
public import CFSG.ClassicalInvolution.AschTight.S1916Coh
public import CFSG.ClassicalInvolution.AschTight.S1916FusStmt
public import CFSG.ClassicalInvolution.AschTight.S1916Inv

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem not_forall_inv_of_not_mem [IsSimpleGroup G] (hDT : Sec19DataT p f K z S W L t V)
    {s : G} (hsS : s ∈ (S : Subgroup G)) (hsX : s ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ¬ ∀ u ∈ K ⊓ W, s * u * s⁻¹ = u⁻¹ := by
  intro hinv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hDT.toSec19Data
  have ht := hd.tight
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := Hall196.exists_data_of_tightBranchD ht
  obtain ⟨k, hkR, hkt⟩ := S1911.exists_conj_eq_mul hDT
  have hkinv := S1911.conj_eq_inv_of_conj_eq_mul hDT hkR hkt
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
    hd.hSz.trans (sd_normalizer_eq hd).ge
  have haS : s * k ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hsS hkR.1
  have haN : s * k ∈ Subgroup.normalizer (K : Set G) := hSN haS
  have hac : ∀ y ∈ (S : Subgroup G) ⊓ K ⊓ W, s * k * y = y * (s * k) := by
    intro y hy
    have hyU : y ∈ K ⊓ W := ⟨hy.1.2, hy.2⟩
    have h1 : (s * k) * y * (s * k)⁻¹ = y := by
      calc (s * k) * y * (s * k)⁻¹ = s * (k * y * k⁻¹) * s⁻¹ := by group
        _ = s * y⁻¹ * s⁻¹ := by rw [hkinv y hyU]
        _ = (s * y * s⁻¹)⁻¹ := by group
        _ = y := by rw [hinv y hyU, inv_inv]
    calc s * k * y = (s * k) * y * (s * k)⁻¹ * (s * k) := by group
      _ = y * (s * k) := by rw [h1]
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' ⟨s * k, haS⟩
  have h2 : orderOf (s * k) = 2 ^ n := by rw [← hn, Subgroup.orderOf_mk]
  have hcard : Nat.card ↥((S : Subgroup G) ⊓ K) ≤ 2 * Nat.card ↥((S : Subgroup G) ⊓ K ⊓ W) := by
    have e1 : (S : Subgroup G) ⊓ K ⊓ W = K ⊓ W := by
      ext x
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hd.hWS h.2, h.1⟩, h.2⟩⟩
    rw [e1, S1911.card_inf_eq hd]
  have hmem : normalizerToPGammaL2Mod e hFcard hF h3 ⟨s * k, haN⟩ ∈
      pGammaL2PGLRange (GaloisField p f) := by
    rcases Nat.even_or_odd f with hfe | hfo
    · exact mem_range_inl_of_centralizes ht.branch.odd ht.branch.five hfe e hFcard hF h3
        (S1911.inf_mem_rSet hd) inf_le_right (S1911.comm_of_mem hd) hcard ⟨n, h2⟩ haN hac
    · refine innerDiagonalTwo_of_odd hfo e hFcard hF h3 ⟨s * k, haN⟩ ?_
      refine IsPGroup.of_card (n := n) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, h2]
  have hX := (psi_mem_iff hd e hFcard hF h3 ⟨s * k, haN⟩).mp hmem
  apply hsX
  have hkX : k ∈ sec19X K z := le_sec19X hd.tight.branch.member hkR.2
  have e2 : s = (s * k) * k⁻¹ := by group
  rw [e2]
  exact Subgroup.mul_mem _ hX (Subgroup.mem_sup_left ((sec19X K z).inv_mem hkX))

theorem mem_or_of_centralizes [IsSimpleGroup G] (h11b : C19_11bTmp p f)
    (hDT : Sec19DataT p f K z S W L t V) (hinv : ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    {q : G} (hqS : q ∈ (S : Subgroup G)) (hqR : ∀ r ∈ (S : Subgroup G) ⊓ K, q * r = r * q)
    (hqt : q * t * q⁻¹ = z * t) {c : G} (hcS : c ∈ (S : Subgroup G))
    (hcR : ∀ r ∈ (S : Subgroup G) ⊓ K, c * r = r * c) :
    c ∈ W ⊓ sec19Y K z ∨ q⁻¹ * c ∈ W ⊓ sec19Y K z := by
  have hd := hDT.toSec19Data
  have htS : t ∈ (S : Subgroup G) := hd.hWS (S1911.mem_W hDT)
  have htz : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz htS)
  rcases conj_t_eq_or_of_mem_centralizer hDT hinv hcS hcR with h | h
  · left
    refine mem_W_inf_of_mem_centralizer_t h11b hDT hcS hcR ?_
    calc c * t = c * t * c⁻¹ * c := by group
      _ = t * c := by rw [h]
  · right
    have hct : c * t = t * z * c := by
      calc c * t = c * t * c⁻¹ * c := by group
        _ = t * z * c := by rw [h]
    have htq : t * q⁻¹ = q⁻¹ * (z * t) := by
      calc t * q⁻¹ = q⁻¹ * (q * t * q⁻¹) := by group
        _ = q⁻¹ * (z * t) := by rw [hqt]
    refine mem_W_inf_of_mem_centralizer_t h11b hDT
      ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hqS) hcS) (fun r hr => ?_) ?_
    · have h1 := hqR r hr
      have h2 := hcR r hr
      have h3 : q⁻¹ * r = r * q⁻¹ := by
        calc q⁻¹ * r = q⁻¹ * (r * q) * q⁻¹ := by group
          _ = q⁻¹ * (q * r) * q⁻¹ := by rw [h1]
          _ = r * q⁻¹ := by group
      calc q⁻¹ * c * r = q⁻¹ * (c * r) := by group
        _ = q⁻¹ * (r * c) := by rw [h2]
        _ = (q⁻¹ * r) * c := by group
        _ = (r * q⁻¹) * c := by rw [h3]
        _ = r * (q⁻¹ * c) := by group
    · calc q⁻¹ * c * t = q⁻¹ * (c * t) := by group
        _ = q⁻¹ * (t * z * c) := by rw [hct]
        _ = q⁻¹ * (z * t) * c := by rw [htz]; group
        _ = t * q⁻¹ * c := by rw [htq]
        _ = t * (q⁻¹ * c) := by group

theorem exists_involution_of_not_le [IsSimpleGroup G] (h11b : C19_11bTmp p f)
    (hDT : Sec19DataT p f K z S W L t V) (hinv : ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    (hPC : ¬ (S : Subgroup G) ⊓ sec19Y K z ≤ W ⊓ sec19Y K z)
    (hS : ¬ (S : Subgroup G) ≤ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ a ∈ (S : Subgroup G), a * a = 1 ∧ a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hDT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have ef := S1911.etaYForm p f G K z S W L t V hDT
  have hKX : K ≤ sec19X K z := le_sec19X hd.tight.branch.member
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
    hd.hSz.trans (sd_normalizer_eq hd).ge
  obtain ⟨-, -, -, hVcyc, -⟩ := hDT.memV
  have hcomm : ∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, ∀ w ∈ W,
      x * w * x⁻¹ * w⁻¹ ∈ W ⊓ sec19Y K z := by
    intro x hx w hw
    refine ⟨W.mul_mem ((Subgroup.mem_normalizer_iff.mp (ef.normalizes hx) w).mp hw)
      (W.inv_mem hw), ?_⟩
    have hw' : w * x⁻¹ * w⁻¹ ∈ sec19Y K z := by
      rw [← Hall196.conjSub_sec19Y hd.tight (hd.hSz (hd.hWS hw))]
      exact conj_mem_conjSub (Subgroup.inv_mem _ hx.2)
    have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx.2 hw'
  have hstar : ∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, x * t = t * x → x ∈ W ⊓ sec19Y K z :=
    fun x hx hxt => mem_W_inf_of_mem_centralizer_t h11b hDT hx.1
      (fun r hr => (sd_commute_R_Q hd r hr x hx).symm) hxt
  have hCP : W ⊓ sec19Y K z ≤ (S : Subgroup G) ⊓ sec19Y K z := inf_le_inf_right _ hd.hWS
  have hC4 : 4 ≤ Nat.card ↥(W ⊓ sec19Y K z) := ef.card ▸ ef.four
  have hC2 : IsPGroup 2 ↥(W ⊓ sec19Y K z) := S.isPGroup'.to_le (inf_le_left.trans hd.hWS)
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le (hDT.leW.trans hd.hWS)
  obtain ⟨q, hqP, hqC, zc, -, -, -, hzcu, hqt, hqinv, -, hq2, -, -, -⟩ :=
    Hall196.exists_swap_of_not_le ef.comm hDT.leW inf_le_left ef.cyclic hVcyc ef.card.symm hC4
      hC2 hV2 hDT.memT hDT.invL.ne_one hDT.invL.sq hCP ef.normalizes hcomm hstar hPC
  have hzW := Hall196.mem_W_of_sec19DataT hDT
  have hzz : z = zc := (hzcu z ⟨hzW, sd_mem_Y hd⟩ hI.sq).resolve_left hI.ne_one
  rw [← hzz] at hq2 hqt
  have hqR : ∀ r ∈ (S : Subgroup G) ⊓ K, q * r = r * q := fun r hr =>
    (sd_commute_R_Q hd r hr q hqP).symm
  have hmemC := fun c hcS hcR => mem_or_of_centralizes h11b hDT hinv hqP.1 hqR hqt (c := c) hcS hcR
  obtain ⟨s, hsS, hsX, hs2⟩ := exists_sq_mem_cStar hd hS
  have hsN : ∀ g ∈ (S : Subgroup G), ∀ x ∈ W ⊓ sec19Y K z, g * x * g⁻¹ ∈ W ⊓ sec19Y K z :=
    fun g hg x hx => ⟨hinv g hg ▸ conj_mem_conjSub hx.1,
      Hall196.conjSub_sec19Y hd.tight (hd.hSz hg) ▸ conj_mem_conjSub hx.2⟩
  have hSR : ∀ g ∈ (S : Subgroup G), ∀ r ∈ (S : Subgroup G) ⊓ K,
      g * r * g⁻¹ ∈ (S : Subgroup G) ⊓ K := fun g hg r hr =>
    ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hg hr.1) ((S : Subgroup G).inv_mem hg),
      (Subgroup.mem_normalizer_iff.mp (hSN hg) r).mp hr.2⟩
  have hcentR : ∀ c, (∀ r ∈ (S : Subgroup G) ⊓ K, c * r = r * c) →
      ∀ g ∈ (S : Subgroup G), ∀ r ∈ (S : Subgroup G) ⊓ K,
        g * c * g⁻¹ * r = r * (g * c * g⁻¹) := by
    intro c hcR g hg r hr
    have hr' : g⁻¹ * r * g ∈ (S : Subgroup G) ⊓ K := by
      have := hSR g⁻¹ ((S : Subgroup G).inv_mem hg) r hr
      rwa [inv_inv] at this
    have h1 := hcR _ hr'
    calc g * c * g⁻¹ * r = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by rw [h1]
      _ = r * (g * c * g⁻¹) := by group
  have hs2S : s * s ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hsS hsS
  have hs2R := mem_centralizer_of_mem_cStar hd hs2S hs2
  have hs2' := hmemC _ hs2S hs2R
  have hsq' : q⁻¹ * (s * q * s⁻¹) ∈ W ⊓ sec19Y K z := by
    have hsqS : s * q * s⁻¹ ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hsS hqP.1) ((S : Subgroup G).inv_mem hsS)
    rcases hmemC _ hsqS (hcentR q hqR s hsS) with h | h
    · exfalso
      apply hqC
      have h2 := hsN s⁻¹ ((S : Subgroup G).inv_mem hsS) _ h
      have e : s⁻¹ * (s * q * s⁻¹) * s⁻¹⁻¹ = q := by group
      rwa [e] at h2
    · exact h
  have hsz : s * z * s⁻¹ = z := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hsS) : s * z = z * s)]
    group
  have hzZ := isUniqueInvolution_W_inf hDT
  obtain ⟨c, hc, hcnorm⟩ := exists_norm_mem_of_dihedral ef.cyclic hC2 hzZ
    (fun x hx y hy => ef.comm x hx.1 y hy.1)
    (exists_mul_self_eq_of_isCyclic hzZ le_rfl ef.cyclic hC2 hC4) hqinv hq2 (hsN s hsS) hsz
    hsq' hs2'
  have hcSY : c ∈ (S : Subgroup G) ⊓ sec19Y K z := by
    rcases hc with h | h
    · exact hCP h
    · have := ((S : Subgroup G) ⊓ sec19Y K z).mul_mem hqP (hCP h)
      rwa [mul_inv_cancel_left] at this
  have hcR : ∀ r ∈ (S : Subgroup G) ⊓ K, c * r = r * c := fun r hr =>
    (sd_commute_R_Q hd r hr c hcSY).symm
  have hcX : c ∈ sec19X K z := sec19Y_le_sec19X K z hcSY.2
  have hθcR := hcentR c hcR s hsS
  have hzU : IsUniqueInvolution (K ⊓ W) z :=
    ⟨⟨hI.mem, hzW⟩, hI.ne_one, hI.sq, fun y hy hy2 => hI.unique y hy.1 hy2⟩
  have hsU : ∀ u ∈ K ⊓ W, s * u * s⁻¹ ∈ K ⊓ W := fun u hu =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hSN hsS) u).mp hu.1, hinv s hsS ▸ conj_mem_conjSub hu.2⟩
  obtain ⟨u, huU, hu⟩ := exists_conj_mul_eq_of_not_inv
    (S.isPGroup'.to_le (inf_le_right.trans hd.hWS)) hzU (fun x hx y hy => ef.comm x hx.2 y hy.2)
    hsU (not_forall_inv_of_not_mem hDT hsS hsX)
  rcases hcnorm with h1 | h1
  · refine ⟨s * c, (S : Subgroup G).mul_mem hsS hcSY.1, ?_, fun hmem => hsX ?_⟩
    · calc s * c * (s * c) = s * c * s⁻¹ * (s * s) * c := by group
        _ = 1 := h1
    · have e : s = s * c * c⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hmem (Subgroup.mem_sup_left ((sec19X K z).inv_mem hcX))
  · have huR : u ∈ (S : Subgroup G) ⊓ K := ⟨hd.hWS huU.2, huU.1⟩
    refine ⟨s * u * c, (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hsS huR.1) hcSY.1, ?_,
      fun hmem => hsX ?_⟩
    · have hc1 := hθcR u huR
      have hc2 := hs2R u huR
      calc s * u * c * (s * u * c)
          = (s * u * s⁻¹) * ((s * c * s⁻¹) * ((s * s) * u)) * c := by group
        _ = (s * u * s⁻¹) * ((s * c * s⁻¹) * (u * (s * s))) * c := by rw [hc2]
        _ = (s * u * s⁻¹) * (((s * c * s⁻¹) * u) * (s * s)) * c := by group
        _ = (s * u * s⁻¹) * ((u * (s * c * s⁻¹)) * (s * s)) * c := by rw [hc1]
        _ = (s * u * s⁻¹ * u) * (s * c * s⁻¹ * (s * s) * c) := by group
        _ = 1 := by rw [hu, h1, hI.sq]
    · have e : s = s * u * c * c⁻¹ * u⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmem
        (Subgroup.mem_sup_left ((sec19X K z).inv_mem hcX)))
        (Subgroup.mem_sup_left ((sec19X K z).inv_mem (hKX huU.1)))

variable (p f) in
theorem exists_involution_of_sec19Data (h11b : C19_11bTmp p f) (hSC : C19_14SCTmp p f)
    (hB3 : GoldschmidtB3Tmp) (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G)
    (z : G) (S : Sylow 2 G) (W : Subgroup G) (hd : Sec19Data p f K z S W)
    (hS : ¬ (S : Subgroup G) ≤ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ a ∈ (S : Subgroup G), a * a = 1 ∧ a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K := by
  obtain ⟨W₀, hd₀, hinv, -, -⟩ := exists_invariant_W hd
  obtain ⟨L, t, V, hDT⟩ := exists_sec19DataT hd₀
  refine exists_involution_of_not_le h11b hDT hinv (fun h => ?_) hS
  have : IsCyclic ↥(W₀ ⊓ sec19Y K z) := S1911.isCyclic_inf_sec19Y hDT
  exact not_case2_of p f hSC hB3 G K z S W₀ hd₀
    (Hall196.sup_eq_oddCoreOf_sup_of_isCyclic (sd_isSylow2In_Q hd₀)
      (Subgroup.isCyclic_of_le h) (h.trans inf_le_left))

variable (p f) in
theorem c19_16Inv_of (h11b : C19_11bTmp p f) (hSC : C19_14SCTmp p f)
    (hB3 : GoldschmidtB3Tmp) : C19_16InvTmp p f :=
  fun G _ _ _ K z S W hd _ hS => exists_involution_of_sec19Data p f h11b hSC hB3 G K z S W hd hS

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
