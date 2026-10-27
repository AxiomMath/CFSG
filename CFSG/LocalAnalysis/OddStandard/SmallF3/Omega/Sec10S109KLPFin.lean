module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPInn
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1010
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L106Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Ca
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cc

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem KLCoord.isElemAbelian {B : Subgroup G} {φ : (Fin 5 → ZMod 2) → G} (hc : KLCoord B φ) :
    CFSG.Open.IsElemAbelian 2 B := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨v, hv, hva⟩ := (hc.mem a.1).1 a.2
    obtain ⟨w, hw, hwb⟩ := (hc.mem b.1).1 b.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hva, ← hwb]
    exact hc.comm hv hw
  · rw [pow_two]
    exact hc.sq_eq_one hx

theorem kl_sup_zpowers_mul {B : Subgroup G} {t u : G} (hu : u ∈ B) :
    B ⊔ zpowers (t * u) = B ⊔ zpowers t := by
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_left hu)
  · rw [Subgroup.zpowers_le]
    have hu' : u ∈ B ⊔ zpowers (t * u) := Subgroup.mem_sup_left hu
    have h := Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers (t * u)))
      (Subgroup.inv_mem _ hu')
    rwa [mul_inv_cancel_right] at h

theorem kl_z_weight4 [Finite G] (hf : Asc82Facts10) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2)
    {φ : (Fin 5 → ZMod 2) → G} (hc : KLCoord (secB S L) φ)
    (h2 : ∀ v, IsEvenVec v → vecWeight v = 2 → ¬ IsI4PlusIn L (φ v)) :
    ∃ vz, IsEvenVec vz ∧ vecWeight vz = 4 ∧ φ vz = z := by
  obtain ⟨vz, hvz, hzφ⟩ := (hc.mem z).1 (sec10C_z_mem_secB hf hb hctx)
  refine ⟨vz, hvz, ?_, hzφ⟩
  rcases even_weight_cases_five vz hvz with h0 | h02 | h04
  · exfalso
    have hz := hctx.pocket.1
    rw [← hzφ, h0, hc.map_zero, orderOf_one] at hz
    omega
  · exfalso
    have hp : IsI4PlusIn L (φ vz) := by
      rw [hzφ]
      exact hctx.pocket
    exact h2 vz hvz h02 hp
  · exact h04

theorem kl_final [Finite G] (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} {g : G}
    (hctx : Sec109Ctx G t L S z K1 K2 g) {m : G} (hm : m ∈ secM t S L)
    (hmt : m⁻¹ * t * m = t * z) : False := by
  obtain ⟨hpsp, htC, htL, htS, hSN, hsyl⟩ := hb G t L S z hctx.toSec10Z
  obtain ⟨ht2, hz2, -⟩ := sec10D_basic hb hctx.toSec10Ctx
  obtain ⟨r, hrS, hr2, hrty, hne, hX, hconj⟩ := sec10C_exists_A2 h.l107c hctx
  have hec : g * m⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : g * m⁻¹ * t * (g * m⁻¹)⁻¹ = t := by
      calc g * m⁻¹ * t * (g * m⁻¹)⁻¹ = g * (m⁻¹ * t * m) * g⁻¹ := by group
        _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [hmt, hctx.swap]
        _ = t := by group
    calc g * m⁻¹ * t = (g * m⁻¹ * t * (g * m⁻¹)⁻¹) * (g * m⁻¹) := by group
      _ = t * (g * m⁻¹) := by rw [hcomm]
  have hecN : g * m⁻¹ ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h3.l36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB _ hec
  have hrA2 : r ∈ secA2 t r K1 K2 :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers r))
  rw [← hconj] at hrA2
  have h1 : g * r * g⁻¹ ∈ secA t S L := (mem_conjugate_iff _ _ _).1 hrA2
  have hAn : IsNormalE32In S (secA t S L) := (hX _).mpr (Or.inl rfl)
  have hAn' := (Subgroup.normal_subgroupOf_iff hAn.1).mp hAn.2.2
  have hsqS : g * g ∈ S := sec10C_g_sq_mem_S hz2 hctx
  have h2 : g⁻¹ * r * g ∈ secA t S L := by
    have := hAn' _ ((g * g)⁻¹) h1 (S.inv_mem hsqS)
    have e : (g * g)⁻¹ * (g * r * g⁻¹) * (g * g)⁻¹⁻¹ = g⁻¹ * r * g := by group
    rwa [e] at this
  have hmA : m * (g⁻¹ * r * g) * m⁻¹ ∈ secA t S L := (Subgroup.mem_normalizer_iff.mp hm _).mp h2
  have hrr : r = (g * m⁻¹) * (m * (g⁻¹ * r * g) * m⁻¹) * (g * m⁻¹)⁻¹ := by group
  have hAin : secA t S L ≤ L ⊔ centralizer (L : Set G) :=
    sup_le ((secB_le_L S L).trans le_sup_left)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right htC))
  have hrinner : InnerOn L r := by
    have := kl_innerOn_conj hecN (hAin hmA)
    rwa [← hrr] at this
  have hrr1 : r * r = 1 := by
    have := pow_orderOf_eq_one r
    rwa [hr2, pow_two] at this
  exact ((hf.factsC.ty G L hpsp r (hSN hrS) (by rw [hrr1]; exact Subgroup.one_mem _)).mpr
    (Or.inr hrty)) hrinner

theorem kl_core [Finite G] (hE : Asc82FactCE16) (h3 : Asc82Sec3Res10) (h : Asc82Res10a)
    (hf : Asc82Facts10) (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} {g : G} (hctx : Sec109Ctx G t L S z K1 K2 g)
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (L ⊓ normalizer (secB S L : Set G))
      (alternatingGroup (Fin 5)))
    (h4 : ∀ v, IsEvenVec v → vecWeight v = 4 → IsI4PlusIn L (φ v))
    (h2 : ∀ v, IsEvenVec v → vecWeight v = 2 → ¬ IsI4PlusIn L (φ v))
    (hBL : secB S L ≤ L) (hB16 : Nat.card (secB S L) = 2 ^ 4) {k : G}
    (hk : k⁻¹ * t * k = t * φ klV0) : False := by
  classical
  obtain ⟨hpsp, htC, htL, htS, hSN, hsyl⟩ := hb G t L S z hctx.toSec10Z
  have hctx10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  obtain ⟨htt, hzz, -⟩ := sec10D_basic hb hctx10
  have hLt : L ≤ centralizer ({t} : Set G) := hctx10.component.le
  have hc : KLCoord (secB S L) φ := KLCoord.of_perm hperm
  have hBE : CFSG.Open.IsElemAbelian 2 (secB S L) := hc.isElemAbelian
  have hB16' : Nat.card (secB S L) = 16 := by rw [hB16]; norm_num
  obtain ⟨u, hudef⟩ : ∃ u, u = φ klV0 := ⟨_, rfl⟩
  rw [← hudef] at hk
  have hu : u ∈ secB S L := by rw [hudef]; exact hc.mem_of_even kl_isEven_v0
  have hu2 : u * u = 1 := by rw [hudef]; exact hc.mul_self kl_isEven_v0
  obtain ⟨t', ht'def⟩ : ∃ t', t' = k⁻¹ * t * k := ⟨_, rfl⟩
  have hk' : t' = t * u := ht'def.trans hk
  obtain ⟨L', hL'def⟩ : ∃ L', L' = CFSG.conjugate L k := ⟨_, rfl⟩
  have hctx' : Sec10Ctx G t' L' (CFSG.conjugate S k) (k⁻¹ * z * k) (CFSG.conjugate K1 k)
      (CFSG.conjugate K2 k) := by
    rw [hL'def, ht'def]
    exact hctx10.conjugate k
  have hS3' : Sec3SettingLB G t' L' := hctx'.toSec10Z.toSec10Setting.toSec3SettingLB
  have hL'psp : IsPSp43 L' := by rw [hL'def]; exact isPSp43_conjugate hpsp k
  have hL't' : L' ≤ centralizer ({t'} : Set G) := hctx'.component.le
  have hN : ∀ c ∈ centralizer ({t'} : Set G), c ∈ normalizer (L' : Set G) :=
    sec4_mem_normalizer h3.l36 hS3'
  have ht'2 : orderOf t' = 2 := hctx'.involution
  have ht'L : t' ∉ L' := (hb G t' L' _ _ hctx'.toSec10Z).2.2.1
  have hsqt' : t' * t' = 1 := by
    have := pow_orderOf_eq_one t'
    rwa [ht'2, pow_two] at this
  have hLC' : L' ⊓ centralizer (L' : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_psp43 hctx'.component.isQuasisimple hL'psp
  have htwo' : ∀ w ∈ centralizer ({t'} : Set G), w ∈ centralizer (L' : Set G) →
      IsPGroup 2 (zpowers w) → w ∈ zpowers t' :=
    fun w hwt hwL hw2 => sec10C_two_elem_R h3.l36 h.l106 hctx' hwt hwL hw2
  have hBt' : secB S L ≤ centralizer ({t'} : Set G) := by
    intro b hb'
    rw [Subgroup.mem_centralizer_singleton_iff, hk']
    have hbt : b * t = t * b := Subgroup.mem_centralizer_iff.mp htC b (hBL hb')
    have hbu : b * u = u * b := by
      obtain ⟨v, hv, rfl⟩ := (hc.mem b).1 hb'
      rw [hudef]
      exact hc.comm hv kl_isEven_v0
    calc b * (t * u) = (b * t) * u := by group
      _ = (t * b) * u := by rw [hbt]
      _ = t * (b * u) := by group
      _ = t * (u * b) := by rw [hbu]
      _ = (t * u) * b := by group
  have ht'B : t' ∉ secB S L := by
    intro hmem
    apply htL
    have e : t = t' * u⁻¹ := by rw [hk']; group
    rw [e]
    exact L.mul_mem (hBL hmem) (L.inv_mem (hBL hu))
  have hBN' : secB S L ≤ normalizer (L' : Set G) := fun b hb' => hN b (hBt' hb')
  have hBC' : secB S L ⊓ centralizer (L' : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro w ⟨hwB, hwC⟩
    have hwz : w ∈ zpowers t' :=
      htwo' w (hBt' hwB) hwC (kl_pgroup_zpowers (hc.sq_eq_one hwB))
    rcases sec10D_eq_one_or_of_mem_zpowers hsqt' hwz with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hwB) ht'B
  have hY : KLStab L' φ := by
    intro σ hσ hσ0
    obtain ⟨m, hm, hmact⟩ := hperm.2.2.2.2 σ hσ
    have hmu : m * u * m⁻¹ = u := by
      rw [hudef, hmact _ kl_isEven_v0, hσ0]
    have hmu' : m * u = u * m := by
      calc m * u = (m * u * m⁻¹) * m := by group
        _ = u * m := by rw [hmu]
    have hmt : m * t = t * m := Subgroup.mem_centralizer_iff.mp htC m hm.1
    have hmt' : m * t' = t' * m := by
      rw [hk']
      calc m * (t * u) = (m * t) * u := by group
        _ = t * (m * u) := by rw [hmt]; group
        _ = t * (u * m) := by rw [hmu']
        _ = (t * u) * m := by group
    exact ⟨m, hN m (Subgroup.mem_centralizer_singleton_iff.mpr hmt'), hmact⟩
  obtain ⟨vz, hvz, hvz4, hzφ⟩ := kl_z_weight4 hf hb hctx10 hc h2
  have hz'4 : IsI4PlusIn L' (k⁻¹ * z * k) := by
    rw [hL'def]
    exact hctx10.pocket.conjugate k
  have hz_not : ∀ i : Fin 5, ¬ InducesTypeSome L' (φ (klF i)) 5 1 4 (-1) := by
    intro i hty
    obtain ⟨σ, hσ, hσv⟩ := exists_alt_permVec_weight_four vz (klF i) hvz4 (kl_weight_F i)
    obtain ⟨l, hl, hlact⟩ := hperm.2.2.2.2 σ hσ
    have hlz : l * z * l⁻¹ = φ (klF i) := by rw [← hzφ, hlact _ hvz, hσv]
    have e : (k⁻¹ * l⁻¹)⁻¹ * (k⁻¹ * z * k) * (k⁻¹ * l⁻¹) = φ (klF i) := by
      rw [← hlz]
      group
    have hmem : (k⁻¹ * l⁻¹)⁻¹ * (k⁻¹ * z * k) * (k⁻¹ * l⁻¹) ∈ centralizer ({t'} : Set G) := by
      rw [e]
      exact hBt' (hc.mem_of_even (kl_isEven_F i))
    have h37 := h3.l37 G t' L' hS3' (k⁻¹ * z * k) (k⁻¹ * l⁻¹) hz'4 hmem
    rw [e] at h37
    exact hf.factsC.lay G L' hL'psp (φ (klF i)) hty h37
  have hinner := kl_inner_of hE hf.factsC.ty hf.out5 hL'psp hc hBN' hBC' hB16' hY (hz_not 0)
    (hz_not 1)
  have hAA : secB S L ⊔ zpowers t' = secA t S L := by
    rw [hk']
    exact kl_sup_zpowers_mul hu
  have h1010 := (asc82Lemma1010_of h.l105 h.l108 hb hf G t L S z K1 K2 hctx10).1
  obtain ⟨-, φ', hperm', h4', h2'⟩ := kl_inn_le hf.b5 hL'psp hLC' ht'2 ht'L hL't' hBE hB16' hBt'
    ht'B htwo' hinner (fun n hn b hb' => h1010 n (by rw [hAA] at hn; exact hn) b hb')
  have hTwo : KLTwo L' (secB S L) φ φ' := ⟨hc, hperm', h4', h2', hY⟩
  obtain ⟨n, hn, hn0, hn1⟩ := kl_swap_pair hTwo
  have hnM : n ∈ secM t S L := by
    show n ∈ normalizer ((secA t S L : Subgroup G) : Set G)
    rw [← hAA]
    exact kl_mem_normalizer_sup hn.2 (kl_mem_normalizer_zpowers (hL't' hn.1))
  have hnt' : n * t' = t' * n := Subgroup.mem_centralizer_singleton_iff.mp (hL't' hn.1)
  have hu01 : u = φ (klF 0) * φ (klF 1) := by
    rw [hudef, ← hc.add _ _ (kl_isEven_F 0) (kl_isEven_F 1), kl_F_add_01]
  have hz4 : φ (klF 0) * φ (klF 1) * φ (klF 2) * φ (klF 3) = φ (klF 4) := by
    calc φ (klF 0) * φ (klF 1) * φ (klF 2) * φ (klF 3)
        = φ (klF 0 + klF 1) * φ (klF 2) * φ (klF 3) := by
          rw [hc.add _ _ (kl_isEven_F 0) (kl_isEven_F 1)]
      _ = φ (klF 0 + klF 1 + klF 2) * φ (klF 3) := by
          rw [hc.add _ _ (kl_even_add (kl_isEven_F 0) (kl_isEven_F 1)) (kl_isEven_F 2)]
      _ = φ (klF 0 + klF 1 + klF 2 + klF 3) := by
          rw [hc.add _ _ (kl_even_add (kl_even_add (kl_isEven_F 0) (kl_isEven_F 1))
            (kl_isEven_F 2)) (kl_isEven_F 3)]
      _ = φ (klF 4) := by rw [kl_F_add_0123]
  have ht_eq : t = t' * u := by
    rw [hk', mul_assoc, hu2, mul_one]
  have hnt : n * t * n⁻¹ = t * φ (klF 4) := by
    have e1 : n * t' * n⁻¹ = t' := by rw [hnt']; group
    have e2 : n * u * n⁻¹ = φ (klF 2) * φ (klF 3) := by
      rw [hu01]
      calc n * (φ (klF 0) * φ (klF 1)) * n⁻¹ = (n * φ (klF 0) * n⁻¹) * (n * φ (klF 1) * n⁻¹) := by
            group
        _ = φ (klF 2) * φ (klF 3) := by rw [hn0, hn1]
    calc n * t * n⁻¹ = n * (t' * u) * n⁻¹ := by rw [← ht_eq]
      _ = (n * t' * n⁻¹) * (n * u * n⁻¹) := by group
      _ = t' * (φ (klF 2) * φ (klF 3)) := by rw [e1, e2]
      _ = t * (φ (klF 0) * φ (klF 1) * φ (klF 2) * φ (klF 3)) := by rw [hk', hu01]; group
      _ = t * φ (klF 4) := by rw [hz4]
  obtain ⟨σa, hσa, hσav⟩ := exists_alt_permVec_weight_four (klF 4) vz (kl_weight_F 4) hvz4
  obtain ⟨a, ha, haact⟩ := hperm.2.2.2.2 σa hσa
  have haz : a * φ (klF 4) * a⁻¹ = z := by rw [haact _ (kl_isEven_F 4), hσav, hzφ]
  have haM : a ∈ secM t S L := by
    show a ∈ normalizer ((secA t S L : Subgroup G) : Set G)
    exact kl_mem_normalizer_sup ha.2 (kl_mem_normalizer_zpowers (hLt ha.1))
  have hat : a * t * a⁻¹ = t := by
    rw [Subgroup.mem_centralizer_iff.mp htC a ha.1]
    group
  have hmM : n⁻¹ * a⁻¹ ∈ secM t S L :=
    (secM t S L).mul_mem ((secM t S L).inv_mem hnM) ((secM t S L).inv_mem haM)
  have hmt : (n⁻¹ * a⁻¹)⁻¹ * t * (n⁻¹ * a⁻¹) = t * z := by
    calc (n⁻¹ * a⁻¹)⁻¹ * t * (n⁻¹ * a⁻¹) = a * (n * t * n⁻¹) * a⁻¹ := by group
      _ = a * (t * φ (klF 4)) * a⁻¹ := by rw [hnt]
      _ = (a * t * a⁻¹) * (a * φ (klF 4) * a⁻¹) := by group
      _ = t * z := by rw [hat, haz]
  exact kl_final h3 h hf hb hctx hmM hmt

theorem asc82StepKL_of (hE : Asc82FactCE16) (h3 : Asc82Sec3Res10) (h : Asc82Res10a)
    (hf : Asc82Facts10) (hb : Asc82Basic10) : Asc82StepKL := by
  intro G _ _ t L S z K1 K2 g hctx u huB hu2 hutype hnz hk
  obtain ⟨k, hk⟩ := hk
  obtain ⟨hBL, hB16, hBC, hAL, hML, φ, hperm, h4, h2, hσ⟩ :=
    sec10BData_of hb hf.b5 hctx.toSec10Z
  obtain ⟨hpsp, htC, htL, htS, hSN, hsyl⟩ := hb G t L S z hctx.toSec10Z
  have hc : KLCoord (secB S L) φ := KLCoord.of_perm hperm
  obtain ⟨v, hv, hvu⟩ := (hc.mem u).1 huB
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [hc.map_zero] at hvu
    rw [← hvu, orderOf_one] at hu2
    omega
  have hv2 : vecWeight v = 2 := by
    rcases even_weight_cases_five v hv with h0 | h02 | h04
    · exact absurd h0 hv0
    · exact h02
    · exfalso
      obtain ⟨vz, hvz, hvz4, hzφ⟩ := kl_z_weight4 hf hb hctx.toSec10Ctx hc h2
      obtain ⟨σ, hσ', hσv⟩ := exists_alt_permVec_weight_four vz v hvz4 h04
      obtain ⟨l, hl, hlact⟩ := hperm.2.2.2.2 σ hσ'
      refine hnz l⁻¹ ?_
      rw [inv_inv, ← hzφ, hlact _ hvz, hσv, hvu]
  obtain ⟨σ0, hσ0, hσ0v⟩ := kl_alt_to_v0 v hv2
  obtain ⟨a0, ha0, ha0act⟩ := hperm.2.2.2.2 σ0 hσ0
  have hu' : a0 * u * a0⁻¹ = φ klV0 := by rw [← hvu, ha0act v hv, hσ0v]
  have hk' : (k * a0⁻¹)⁻¹ * t * (k * a0⁻¹) = t * φ klV0 := by
    have ha0t : a0 * t = t * a0 := Subgroup.mem_centralizer_iff.mp htC a0 ha0.1
    have hat : a0 * t * a0⁻¹ = t := by rw [ha0t]; group
    calc (k * a0⁻¹)⁻¹ * t * (k * a0⁻¹) = a0 * (k⁻¹ * t * k) * a0⁻¹ := by group
      _ = a0 * (t * u) * a0⁻¹ := by rw [hk]
      _ = (a0 * t * a0⁻¹) * (a0 * u * a0⁻¹) := by group
      _ = t * φ klV0 := by rw [hat, hu']
  exact kl_core hE h3 h hf hb hctx hperm h4 h2 hBL hB16 hk'

end CFSG.OddStandard.SmallF3.Omega
