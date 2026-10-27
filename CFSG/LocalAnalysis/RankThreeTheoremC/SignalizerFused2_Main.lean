module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerFused2_Struct
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerGeneration
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentralizer
import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Plane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.hasPrimeConstraint_centralizer (hS : Setting G)
    (h : CentralizerGeneration G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : (P : Subgroup G) ≤ normalizer (D : Set G)) {z : G}
    (hzZ : z ∈ (center D).map D.subtype) (hz1 : z ≠ 1) :
    HasPrimeConstraint (G := centralizer ({z} : Set G)) p := by
  by_contra hcon
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hD := (hext.exists_normal_plane hS hp hPD).1
  obtain ⟨hM, -, -, -⟩ := hext.obstruction
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hp hM).2
  obtain ⟨E, hEP, hE, hEc⟩ := pRank_attained p (P : Subgroup G) (by omega)
  rw [hP3] at hEc
  have hzc := hext.center_le_centralizer hprime hodd hD hzZ
  have hPC : (P : Subgroup G) ≤ centralizer ({z} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc g hg)
  have h3 : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({z} : Set G)) := by
    rw [inf_eq_left.mpr hPC, hP3]
  refine hext.centralizer_not_le_of_mem_center hS hp hD hzZ hz1
    ((h p hp P M D hext hPD z hzZ hz1 hcon E hEP hE hEc).trans
      (sup_le (pPrimeCoreIn_centralizer_le hS hp hM h3) ?_))
  exact iSup_le fun y => iSup_le fun hyE => iSup_le fun hyz =>
    hext.inf_centralizer_le hS hp hD hzZ hz1 hEP hE hEc hyE hyz

namespace NoncentralConfig

variable {p : ℕ} {P : Sylow p G} {M D U : Subgroup G} {u : G}

theorem orderOf_center_elt (hc : NoncentralConfig G p P M D U u) {z : G}
    (hzZ : z ∈ (center D).map D.subtype) (hz1 : z ≠ 1) : orderOf z = p :=
  have : Fact p.Prime := ⟨hc.prime⟩
  orderOf_eq_prime (hc.pow_D z (map_subtype_le _ hzZ)) hz1

theorem P_le_centralizer (hc : NoncentralConfig G p P M D U u) {z : G}
    (hzZ : z ∈ (center D).map D.subtype) :
    (P : Subgroup G) ≤ centralizer ({z} : Set G) := fun _ hg =>
  mem_centralizer_singleton_iff.mpr (hc.Z_comm hzZ hg)

theorem fusedCentral (hc : NoncentralConfig G p P M D U u) (hgen : CentralizerGeneration G)
    {z : G} (hzZ : z ∈ (center D).map D.subtype) (hz1 : z ≠ 1) :
    FusedCentral (centralizer ({z} : Set G)) p (P.subtype (hc.P_le_centralizer hzZ))
      ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ := by
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hPC := hc.P_le_centralizer hzZ
  have hMc := hc.ext.obstruction.1
  have hPM := (sylow_le_of_isCoreMaxLocal hc.setting hc.sigma hMc).1
  have hcon := hc.ext.hasPrimeConstraint_centralizer hc.setting hgen hc.sigma hc.PD hzZ hz1
  have hD := hc.nonab
  have hCM := hc.ext.centralizer_not_le_of_mem_center hc.setting hc.sigma hD hzZ hz1
  refine ⟨hprime, hc.odd, ?_, ?_, ?_, layer_eq_bot_of_exists_selfCentralizing hcon, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact hc.orderOf_center_elt hzZ hz1
  · exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  · show (⟨z, _⟩ : centralizer ({z} : Set G)) ∈
      (P.subtype hPC : Subgroup (centralizer ({z} : Set G)))
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    exact hc.D_le_P (map_subtype_le _ hzZ)
  · have hTP : ((P.subtype hPC : Sylow p (centralizer ({z} : Set G))) :
        Subgroup (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype ≤ P := by
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC]
    have hTrank : 3 ≤ CFSG.Open.pRank p (((P.subtype hPC : Sylow p (centralizer ({z} : Set G))) :
        Subgroup (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype) := by
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC, hc.pRank_P]
    have h3 : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer ({z} : Set G)) := by
      rw [inf_eq_left.mpr hPC, hc.pRank_P]
    have hcore : GLBPrimeCore p (centralizer ({z} : Set G)) ≤ M :=
      (glbPrimeCore_le_pPrimeCoreIn p _).trans
        (pPrimeCoreIn_centralizer_le hc.setting hc.sigma hMc h3)
    obtain ⟨Tbar, hTbar, hred⟩ := reducedNongeneration_of_not_le hprime hc.odd P hPM hMc.2 hCM
      (P.subtype hPC) hTP hTrank hcore
    exact ⟨Tbar, _, hTbar, hred⟩

end NoncentralConfig

theorem exists_normalizer_conj_into_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p G) {N : Subgroup G}
    (hPN : (P : Subgroup G) ≤ N) {S : Subgroup G} (hSN : S ≤ N) (hS : IsPGroup p S) :
    ∃ k ∈ N, ∀ s ∈ S, k * s * k⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨T, hT⟩ := (hS.comap_subtype (K := N)).exists_le_sylow
  have hT' : CFSG.ABGLocalTools.IsSylowOf p ((T : Subgroup N).map N.subtype) N := ⟨T, rfl⟩
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) N :=
    ⟨P.subtype hPN, by rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPN]⟩
  obtain ⟨k, hkN, hk⟩ := hT'.exists_mem_conj hPsyl
  refine ⟨k, hkN, fun s hs => ?_⟩
  have hsT : s ∈ (T : Subgroup N).map N.subtype := ⟨⟨s, hSN hs⟩, hT hs, rfl⟩
  refine (hk (k * s * k⁻¹)).mpr ?_
  have : k⁻¹ * (k * s * k⁻¹) * k = s := by group
  rw [this]
  exact hsT

omit [Finite G] in
theorem fused_conj_pow_eq_mul_pow {a u w : G} (h1 : a * u * a⁻¹ = w * u) (h2 : a * w = w * a)
    (h3 : w * u = u * w) (n : ℕ) : a ^ n * u * (a ^ n)⁻¹ = u * w ^ n := by
  have hwa : ∀ m : ℕ, a * w ^ m * a⁻¹ = w ^ m := fun m => by
    rw [(Commute.pow_right h2 m).eq]
    group
  induction n with
  | zero => simp
  | succ n ih =>
    calc a ^ (n + 1) * u * (a ^ (n + 1))⁻¹
        = a * (a ^ n * u * (a ^ n)⁻¹) * a⁻¹ := by group
      _ = a * (u * w ^ n) * a⁻¹ := by rw [ih]
      _ = (a * u * a⁻¹) * (a * w ^ n * a⁻¹) := by group
      _ = (w * u) * w ^ n := by rw [h1, hwa]
      _ = u * w ^ (n + 1) := by rw [h3, mul_assoc, ← pow_succ']

namespace NoncentralConfig

variable {p : ℕ} {P : Sylow p G} {M D U : Subgroup G} {u : G}

theorem exists_conj_eq_mul_zpow (hc : NoncentralConfig G p P M D U u) {z : G}
    (hzZ : z ∈ (center D).map D.subtype) (c : ℤ) :
    ∃ y ∈ (P : Subgroup G), y * u * y⁻¹ = u * z ^ c := by
  obtain ⟨x₀, hx₀P, hx₀⟩ := hc.exists_not_comm
  have hwZ : x₀ * u * x₀⁻¹ * u⁻¹ ∈ (center D).map D.subtype := hc.commutator_mem_Z hx₀P
  have hw1 : x₀ * u * x₀⁻¹ * u⁻¹ ≠ 1 := by
    intro h
    apply hx₀
    have h' : x₀ * u * x₀⁻¹ = u := mul_inv_eq_one.mp h
    calc x₀ * u = x₀ * u * x₀⁻¹ * x₀ := by group
      _ = u * x₀ := by rw [h']
  generalize hw : x₀ * u * x₀⁻¹ * u⁻¹ = w at hwZ hw1
  have hwu' : x₀ * u * x₀⁻¹ = w * u := by rw [← hw]; group
  have hzw : zpowers w = (center D).map D.subtype := hc.zpowers_eq_center hwZ hw1
  have hzc : z ^ c ∈ zpowers w := by
    rw [hzw]
    exact zpow_mem hzZ c
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr hzc : z ^ c ∈ Submonoid.powers w)
  refine ⟨x₀ ^ n, pow_mem hx₀P n, ?_⟩
  have hn' : w ^ n = z ^ c := hn
  rw [fused_conj_pow_eq_mul_pow hwu' (hc.Z_comm hwZ hx₀P) (hc.U_comm (hc.Z_le_U hwZ) hc.uU) n, hn']

end NoncentralConfig

namespace NoncentralConfig

variable {p : ℕ} {P : Sylow p G} {M D U : Subgroup G} {u : G}

theorem false_of_fused (hc : NoncentralConfig G p P M D U u) (hgen : CentralizerGeneration G)
    (hfuse : ∃ g : G, g * u * g⁻¹ ∈ (center D).map D.subtype) : False := by
  classical
  obtain ⟨z, hzZ, hz1, hzord, hzeq⟩ := hc.exists_Z_gen
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  set C₀ : Subgroup G := centralizer ({z} : Set G) with hC₀
  have hPC : (P : Subgroup G) ≤ C₀ := hc.P_le_centralizer hzZ
  have hF := hc.fusedCentral hgen hzZ hz1
  obtain ⟨Tbar, X₀, E, C, hE, e, hT, hrs⟩ := hF.exists_structure
  have hUC : U ≤ C₀ := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hc.U_comm hx (hc.Z_le_U hzZ))
  set B : Subgroup G := omegaOneOf p (R P U) with hB
  have hBP : B ≤ (P : Subgroup G) := B_le_P
  have hBC : B ≤ C₀ := hBP.trans hPC
  have huz : u ∉ zpowers z := by
    rw [hzeq]
    exact hc.uZ
  have hmemP : ∀ x : C₀, x ∈ (P.subtype hPC : Subgroup C₀) ↔ (x : G) ∈ (P : Subgroup G) := by
    intro x
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
  obtain ⟨t, c, hinv, hBt⟩ := hF.exists_reflection hT hrs (U := U.subgroupOf C₀)
    (B := B.subgroupOf C₀) (u := ⟨u, hUC hc.uU⟩)
    (fun x hx => (hmemP x).mpr (hc.U_le_P hx))
    (isElemAbelian_subgroupOf hc.Ue)
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv).trans hc.Uc)
    (fun x hx => by
      have hx' : (x : G) ∈ (P : Subgroup G) := (hmemP x).mp hx
      have h1 : x ∈ (normalizer (U : Set G)).subgroupOf C₀ := hc.PU hx'
      rwa [Subgroup.subgroupOf_normalizer_eq hUC] at h1)
    (hc.Z_le_U hzZ) hc.uU
    (fun h => huz (by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
      exact ⟨m, congrArg Subtype.val hm⟩))
    (fun y => by
      constructor
      · intro hy
        have hy' : (y : G) ∈ B := hy
        refine ⟨(hmemP y).mpr (hBP hy'), ?_, fun x hx => ?_⟩
        · apply Subtype.ext
          show (y : G) ^ p = 1
          exact hc.isElemAbelian_B.2 (y : G) hy'
        · apply Subtype.ext
          exact R_comm_U (B_le_R hy') hx
      · rintro ⟨hyP, hyp, hcomm⟩
        have hyP' : (y : G) ∈ (P : Subgroup G) := (hmemP y).mp hyP
        have hyp' : (y : G) ^ p = 1 := congrArg Subtype.val hyp
        have hyR : (y : G) ∈ R P U := ⟨hyP', mem_centralizer_iff.mpr fun x hx =>
          (congrArg Subtype.val (hcomm ⟨x, hUC hx⟩ hx)).symm⟩
        exact mem_B hyR hyp')
    (fun x hx y hy => by
      have h : (x : G) * y = y * x := congrArg (fun w : B => (w : G))
        (hc.isElemAbelian_B.1.is_comm.comm ⟨(x : G), hx⟩ ⟨(y : G), hy⟩)
      exact Subtype.ext h)
  set tG : G := (t : G) with htG
  set u₀ : G := u * z ^ c with hu₀
  have ht1 : tG * u₀ * tG⁻¹ = u₀⁻¹ := by
    have := congrArg Subtype.val hinv
    simpa [hu₀, htG] using this
  have htB : ∀ b ∈ B, ∃ i : ℤ, tG * b * tG⁻¹ = b * u₀ ^ i := by
    intro b hb
    obtain ⟨i, hi⟩ := hBt ⟨b, hBC hb⟩ hb
    refine ⟨i, ?_⟩
    have := congrArg Subtype.val hi
    simpa [hu₀, htG] using this
  obtain ⟨y, hyP, hyu⟩ := hc.exists_conj_eq_mul_zpow hzZ c
  obtain ⟨g, hg⟩ := hfuse
  set g₀ : G := g * y⁻¹ with hg₀
  set w₀ : G := g * u * g⁻¹ with hw₀
  have hg₀u : g₀ * u₀ * g₀⁻¹ = w₀ := by rw [hu₀, ← hyu, hg₀, hw₀]; group
  have hw₀1 : w₀ ≠ 1 := by
    intro h
    apply hc.u1
    have h' : g * u * g⁻¹ = 1 := h
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group
  have hw₀z : zpowers w₀ = zpowers z := by rw [hc.zpowers_eq_center hg hw₀1, hzeq]
  set N₀ : Subgroup G := normalizer ((zpowers z : Subgroup G) : Set G) with hN₀
  have hCN : C₀ ≤ N₀ := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_eq_closure, centralizer_closure]
  have hPN₀ : (P : Subgroup G) ≤ N₀ := hPC.trans hCN
  have hu₀U : u₀ ∈ U := U.mul_mem hc.uU (zpow_mem (hc.Z_le_U hzZ) c)
  set S : Subgroup G := (R P U).map (MulAut.conj g₀).toMonoidHom with hS
  have hSN : S ≤ N₀ := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : r * u₀ = u₀ * r := R_comm_U hr hu₀U
    have hcent : g₀ * r * g₀⁻¹ ∈ centralizer ({w₀} : Set G) := by
      refine mem_centralizer_singleton_iff.mpr ?_
      rw [← hg₀u]
      calc g₀ * r * g₀⁻¹ * (g₀ * u₀ * g₀⁻¹) = g₀ * (r * u₀) * g₀⁻¹ := by group
        _ = g₀ * (u₀ * r) * g₀⁻¹ := by rw [h1]
        _ = (g₀ * u₀ * g₀⁻¹) * (g₀ * r * g₀⁻¹) := by group
    have hcn : centralizer ({w₀} : Set G) ≤ normalizer ((zpowers w₀ : Subgroup G) : Set G) := by
      refine le_trans ?_ (centralizer_le_normalizer _)
      rw [zpowers_eq_closure, centralizer_closure]
    have := hcn hcent
    rw [hw₀z] at this
    exact this
  have hSp : IsPGroup p S := by
    obtain ⟨k, hk⟩ := (P.isPGroup'.to_le (inf_le_left : R P U ≤ (P : Subgroup G))).exists_card_eq
    exact IsPGroup.of_card (n := k)
      (by rw [hS, Subgroup.card_map_of_injective (MulAut.conj g₀).injective, hk])
  obtain ⟨c₁, hc₁N, hc₁P⟩ := exists_normalizer_conj_into_sylow P hPN₀ hSN hSp
  set g₁ : G := c₁ * g₀ with hg₁
  have hg₁R : ∀ r ∈ R P U, g₁ * r * g₁⁻¹ ∈ (P : Subgroup G) := fun r hr => by
    have := hc₁P _ ⟨r, hr, rfl⟩
    have e : c₁ * ((MulAut.conj g₀).toMonoidHom r) * c₁⁻¹ = g₁ * r * g₁⁻¹ := by
      rw [hg₁]; simp [MulAut.conj_apply, mul_assoc]
    rwa [e] at this
  set w₁ : G := g₁ * u₀ * g₁⁻¹ with hw₁
  have hw₁z : w₁ ∈ zpowers z := by
    have : w₁ = c₁ * w₀ * c₁⁻¹ := by rw [hw₁, ← hg₀u, hg₁]; group
    rw [this]
    exact (mem_normalizer_iff.mp hc₁N w₀).mp (hw₀z ▸ Subgroup.mem_zpowers w₀)
  have hw₁1 : w₁ ≠ 1 := by
    intro h
    apply hw₀1
    have h' : c₁ * w₀ * c₁⁻¹ = 1 := by rw [← h, hw₁, ← hg₀u, hg₁]; group
    calc w₀ = c₁⁻¹ * (c₁ * w₀ * c₁⁻¹) * c₁ := by group
      _ = 1 := by rw [h']; group
  have hw₁eq : zpowers w₁ = zpowers z := by
    have h1 : w₁ ∈ (center D).map D.subtype := hzeq ▸ hw₁z
    rw [hc.zpowers_eq_center h1 hw₁1, hzeq]
  set t' : G := g₁ * tG * g₁⁻¹ with ht'
  have ht'w : t' * w₁ * t'⁻¹ = w₁⁻¹ := by
    have : t' * w₁ * t'⁻¹ = g₁ * (tG * u₀ * tG⁻¹) * g₁⁻¹ := by rw [ht', hw₁]; group
    rw [this, ht1, hw₁]
    group
  have ht'z : t' * z * t'⁻¹ = z⁻¹ := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (hw₁eq ▸ Subgroup.mem_zpowers z : z ∈ zpowers w₁)
    rw [← hm, ← conj_zpow, ht'w, inv_zpow]
  have ht'N : t' ∈ normalizer ((zpowers z : Subgroup G) : Set G) :=
    mem_normalizer_zpowers_of_conj_mem (by
      rw [ht'z]
      exact inv_mem (Subgroup.mem_zpowers z))
  have hCeq : centralizer ((zpowers z : Subgroup G) : Set G) = C₀ := by
    rw [zpowers_eq_closure, centralizer_closure]
  have ht'C : t' ∈ normalizer (C₀ : Set G) := by
    have := normalizer_le_normalizer_centralizer (zpowers z) ht'N
    rwa [hCeq] at this
  set θ : MulAut C₀ := C₀.normalizerMonoidHom ⟨t', ht'C⟩ with hθ
  have hθc : ∀ x : C₀, ((θ x : C₀) : G) = t' * x * t'⁻¹ := fun x => rfl
  set zH : C₀ := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ with hzH
  have hθz : θ zH = zH ^ (-1 : ℤ) := by
    apply Subtype.ext
    rw [hθc, Subgroup.coe_zpow, zpow_neg_one]
    exact ht'z
  set B' : Subgroup G := B.map (MulAut.conj g₁).toMonoidHom with hB'
  have hB'P : B' ≤ (P : Subgroup G) := by
    rintro _ ⟨b, hb, rfl⟩
    exact hg₁R b (B_le_R hb)
  have hB'C : B' ≤ C₀ := hB'P.trans hPC
  have hB'1 : ∀ x ∈ B'.subgroupOf C₀, x ^ p = 1 := by
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hx
    have hbx' : (x : G) = g₁ * b * g₁⁻¹ := hbx.symm
    apply Subtype.ext
    show (x : G) ^ p = 1
    rw [hbx', conj_pow, hc.isElemAbelian_B.2 b hb]
    group
  have hB'comm : ∀ x ∈ B'.subgroupOf C₀, ∀ y ∈ B'.subgroupOf C₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨b, hb, hbx⟩ := hx
    obtain ⟨b', hb', hby⟩ := hy
    have hbx' : (x : G) = g₁ * b * g₁⁻¹ := hbx.symm
    have hby' : (y : G) = g₁ * b' * g₁⁻¹ := hby.symm
    apply Subtype.ext
    show (x : G) * y = y * x
    rw [hbx', hby']
    have h2 : b * b' = b' * b := congrArg (fun w : B => (w : G))
      (hc.isElemAbelian_B.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
    calc g₁ * b * g₁⁻¹ * (g₁ * b' * g₁⁻¹) = g₁ * (b * b') * g₁⁻¹ := by group
      _ = g₁ * (b' * b) * g₁⁻¹ := by rw [h2]
      _ = g₁ * b' * g₁⁻¹ * (g₁ * b * g₁⁻¹) := by group
  have hB'c : Nat.card (B'.subgroupOf C₀) = p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'C).toEquiv, hB',
      Subgroup.card_map_of_injective (MulAut.conj g₁).injective]
    exact hc.card_B
  have hθB : ∀ b' ∈ B'.subgroupOf C₀, ∃ i : ℤ, θ b' = b' * zH ^ i := by
    intro b' hb'
    obtain ⟨b, hb, hbb'⟩ := hb'
    have hbb'' : (b' : G) = g₁ * b * g₁⁻¹ := hbb'.symm
    obtain ⟨i, hi⟩ := htB b hb
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hw₁z
    refine ⟨j * i, ?_⟩
    apply Subtype.ext
    rw [hθc, Subgroup.coe_mul, Subgroup.coe_zpow]
    show t' * (b' : G) * t'⁻¹ = (b' : G) * z ^ (j * i)
    rw [hbb'']
    have e1 : t' * (g₁ * b * g₁⁻¹) * t'⁻¹ = g₁ * (tG * b * tG⁻¹) * g₁⁻¹ := by rw [ht']; group
    rw [e1, hi]
    have e2 : g₁ * (b * u₀ ^ i) * g₁⁻¹ = (g₁ * b * g₁⁻¹) * w₁ ^ i := by
      rw [hw₁, conj_zpow]
      group
    rw [e2, ← hj, ← zpow_mul]
  have hres := hF.center_fixed θ (-1) hθz (B' := B'.subgroupOf C₀)
    (fun x hx => (hmemP x).mpr (hB'P hx)) hB'1 hB'comm hB'c hθB
  have hz2 : z⁻¹ = z := by
    have := congrArg Subtype.val hres
    simpa [zpow_neg_one] using this
  have hz3 : z ^ 2 = 1 := by
    calc z ^ 2 = z * z := pow_two z
      _ = z * z⁻¹ := by rw [hz2]
      _ = 1 := mul_inv_cancel z
  have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz3
  rw [hzord] at hdvd
  exact hc.odd ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hdvd)
end NoncentralConfig

theorem signalizerNoncentralFused_of_generation (hS : Setting G)
    (hgen : CentralizerGeneration G) : SignalizerNoncentralFused G := by
  intro p hp P M D hext hPD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ U hUD hPU hUe hUc hU3 hNU u huU hu1
    huZ _ hfuse _ _
  exact (NoncentralConfig.false_of_fused (p := p) (P := P) (M := M) (D := D) (U := U) (u := u)
    ⟨hS, hp, hext, hPD, hUD, hPU, hUe, hUc, hU3, hNU, huU, hu1, huZ⟩ hgen hfuse).elim

end CFSG.LocalAnalysis.RankThreeTheoremC
