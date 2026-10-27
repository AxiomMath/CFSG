module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CentConfig
public import Certificates.Certificate725102
public import CFSG.Quasithin.Vol2.KGFactC31RuType32
public import CFSG.Quasithin.Vol2.KGFactC31RuType64
public import CFSG.Quasithin.Vol2.KGFactC31RuTypeE

public section

namespace CFSG.SectionRank.QTK.Insp443.Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Ru

variable {A : Type} [Group A] [Finite A]

theorem pb_comm_sq {V : Subgroup A} (hV : IsElemAbelian 2 V) (e : G₀ ≃* A) :
    (∀ a ∈ pb e V, ∀ b ∈ pb e V, a * b = b * a) ∧ ∀ a ∈ pb e V, a * a = 1 := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨haP, haV⟩ := (mem_pb e).mp ha
    obtain ⟨hbP, hbV⟩ := (mem_pb e).mp hb
    have h1 := hV.1.is_comm.comm ⟨_, haV⟩ ⟨_, hbV⟩
    have h2 : e ⟨a, haP⟩ * e ⟨b, hbP⟩ = e ⟨b, hbP⟩ * e ⟨a, haP⟩ := by
      simpa using congrArg Subtype.val h1
    rw [← map_mul, ← map_mul] at h2
    exact congrArg Subtype.val (e.injective h2)
  · obtain ⟨haP, haV⟩ := (mem_pb e).mp ha
    have h2 := hV.2 _ haV
    rw [sq, ← map_mul, ← map_one e] at h2
    exact congrArg Subtype.val (e.injective h2)

section Five


theorem false_vz_core {L V MK : Subgroup A} (h : KConfig A L V MK) (e : G₀ ≃* A)
    (hUV : img e u32 ≤ V) (hx : e ⟨x32, ruC_le x32_memC⟩ ∈ L) : False := by
  set V' := pb e V with hV'
  set L' := pb e L with hL'
  have hVP : V' ≤ ruP := pb_le e V
  have hUV' : u32 ≤ V' := (le_iff_img_le e (refSub_le_ruP _)).mp hUV
  obtain ⟨hVab, hVsq⟩ := pb_comm_sq h.elemAbelian e
  have hLN : L' ≤ Subgroup.normalizer (V' : Set (Equiv.Perm (Fin 4060))) :=
    pb_le_normalizer e h.le_normalizer
  have hxM : x32 ∈ L' := (apply_mem_iff_mem_pb e).mp hx
  have hV32 : V' ≤ u32 := by
    intro v hv
    refine mem_u32_of (hVP hv) (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      hVab u (hUV' hu) v hv) (hVsq v hv) fun j _ => ?_
    have hc : x32 ^ (j + 1) * v * (x32 ^ (j + 1))⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hLN hxM) _) v).mp hv
    exact hVab v hv _ hc
  have hVeq : pb e V = u32 := le_antisymm hV32 hUV'
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) := by
    refine isPGroup_of_pb e ?_
    rw [pb_centralizer, hVeq]
    intro g
    exact ⟨7, Subtype.ext (by simpa using pow_centralizer32 g.2.1 g.2.2)⟩
  have hNV : Subgroup.normalizer (V : Set A) ≤ Subgroup.normalizer (L : Set A) :=
    (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V).trans (h.normalizer_centralizer_le hC2)
  have hCV : img e ruC ≤ Subgroup.normalizer (V : Set A) := by
    rw [le_iff_img_le e ruC_le, pb_normalizer, hVeq]
    exact le_inf ruC_le ruC_le_normalizer32
  have hLC : L' ≤ ruC := fun m hm => normalizer32_le ⟨pb_le e L hm, hVeq ▸ hLN hm⟩
  have hcN : cQ ∈ Subgroup.normalizer (L' : Set (Equiv.Perm (Fin 4060))) := by
    have h1 : img e ruC ≤ Subgroup.normalizer (L : Set A) := hCV.trans hNV
    rw [le_iff_img_le e ruC_le, pb_normalizer] at h1
    exact (h1 cQ_memC).2
  have hcommM : x32 * cQ * x32⁻¹ * cQ⁻¹ ∈ L' := by
    have h1 : cQ * x32⁻¹ * cQ⁻¹ ∈ L' :=
      (Subgroup.mem_normalizer_iff.mp hcN _).mp (L'.inv_mem hxM)
    have : x32 * cQ * x32⁻¹ * cQ⁻¹ = x32 * (cQ * x32⁻¹ * cQ⁻¹) := by group
    rw [this]
    exact L'.mul_mem hxM h1
  have hcommJ : x32 * cQ * x32⁻¹ * cQ⁻¹ ∈ ruJ := by
    have h1 : x32 * cQ * x32⁻¹ ∈ ruJ :=
      (Subgroup.mem_normalizer_iff.mp (ruC_le_normalizerJ x32_memC) cQ).mp cQ_memJ
    exact ruJ.mul_mem h1 (ruJ.inv_mem cQ_memJ)
  have hJ2 : IsPGroup 2 ↥(img e ruJ) := by
    rw [img]
    exact (isPGroup_ruJ.of_equiv (Subgroup.subgroupOfEquivOfLe (ruJ_leC.trans ruC_le)).symm).map _
  have hLJ : L ≤ Subgroup.normalizer ((img e ruJ : Subgroup A) : Set A) := by
    rw [normalizer_img e (ruJ_leC.trans ruC_le), img_le_iff_le_pb]
    exact le_inf (pb_le e L) (hLC.trans ruC_le_normalizerJ)
  have hJO : L ⊓ img e ruJ ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm) (hLJ hm))
      (hJ2.to_le inf_le_right)
  have hmem : e ⟨_, pb_le e L hcommM⟩ ∈ L ⊓ img e ruJ :=
    ⟨(apply_mem_iff_mem_pb e).mpr hcommM, (apply_mem_img e).mpr hcommJ⟩
  have hC := h.pCoreOf_le (hJO hmem)
  rw [apply_mem_iff_mem_pb e, pb_centralizer, hVeq] at hC
  exact commut_not_mem hC.2

theorem false_vz {L V MK : Subgroup A} (h : KConfig A L V MK) (e : G₀ ≃* A)
    (hUV : img e u32 ≤ V) {y : G₀} (hyM : e y ∈ L)
    (hyN : (y : Equiv.Perm (Fin 4060)) ∈ Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060))))
    (hy : ∃ k : ℕ, y ^ 5 ^ k = 1) (hy1 : y ≠ 1) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hyC : (y : Equiv.Perm (Fin 4060)) ∈ ruC := normalizer32_le ⟨y.2, hyN⟩
  obtain ⟨n, hnC, hxM⟩ := exists_conj_std e ruC_le x32_memC orderOf_x32
    (by rw [card_ruC]; norm_num) hyC hy hy1 hyM
  have hnN : ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060)) ∈
      Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060))) :=
    ruC_le_normalizer32 (by simpa using ruC.inv_mem hnC)
  have e1 : u32.map (MulAut.conj ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060))).toMonoidHom = u32 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
  exact false_vz_core h (conjE e n⁻¹) (by rw [img_conjE, e1]; exact hUV) hxM

theorem false_w16_core {L V MK : Subgroup A} (h : KConfig A L V MK) (e : G₀ ≃* A)
    (hUV : img e u16 ≤ V) (hx : e ⟨x16, wG_mem _⟩ ∈ L) : False := by
  set V' := pb e V with hV'
  set L' := pb e L with hL'
  have hVP : V' ≤ ruP := pb_le e V
  have hUV' : u16 ≤ V' := (le_iff_img_le e (refSub_le_ruP _)).mp hUV
  obtain ⟨hVab, hVsq⟩ := pb_comm_sq h.elemAbelian e
  have hLN : L' ≤ Subgroup.normalizer (V' : Set (Equiv.Perm (Fin 4060))) :=
    pb_le_normalizer e h.le_normalizer
  have hxM : x16 ∈ L' := (apply_mem_iff_mem_pb e).mp hx
  have hVp : V' ≤ uV32p := by
    intro v hv
    refine mem_V32p_of (hVP hv) (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      hVab u (hUV' hu) v hv) (hVsq v hv) fun j _ => ?_
    have hc : x16 ^ (j + 1) * v * (x16 ^ (j + 1))⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hLN hxM) _) v).mp hv
    exact hVab v hv _ hc
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) := by
    refine isPGroup_of_pb e ?_
    rw [pb_centralizer]
    intro g
    exact ⟨7, Subtype.ext (by
      simpa using pow_centralizer16 g.2.1 (Subgroup.centralizer_le hUV' g.2.2))⟩
  have hNL := h.normalizer_centralizer_le hC2
  by_cases hVe : V' = u16
  · have hVe' : pb e V = u16 := hVe
    have hg : g16 ∈ Subgroup.normalizer
        ((ruP ⊓ Subgroup.centralizer (u16 : Set (Equiv.Perm (Fin 4060))) : Subgroup _) :
          Set (Equiv.Perm (Fin 4060))) :=
      mem_normalizer_of_conj_le fun c hc => ⟨ruP.mul_mem (ruP.mul_mem (wG_mem _) hc.1)
        (ruP.inv_mem (wG_mem _)), conj_g16_centralizer16 hc.1 hc.2⟩
    have hgR : e ⟨g16, wG_mem _⟩ ∈
        Subgroup.normalizer ((Subgroup.centralizer (V : Set A) : Subgroup A) : Set A) := by
      rw [← img_pb e (Subgroup.centralizer (V : Set A)), normalizer_img e (pb_le e _),
        pb_centralizer, hVe', apply_mem_img]
      exact ⟨wG_mem _, hg⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (hNL hgR) _).mp hx
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    have h2 := hLN ((apply_mem_iff_mem_pb e).mp h1)
    rw [hVe] at h2
    exact conj_x16_not_mem_normalizer (by simpa using h2)
  ·
    have hVeq : V' = uV32p := by
      have hd := Subgroup.card_dvd_of_le hVp
      rw [card_refSub hvV32p] at hd
      have hge : Nat.card u16 ≤ Nat.card V' := Subgroup.card_le_of_le hUV'
      rw [card_refSub hv16] at hge
      have hne : Nat.card V' ≠ 2 ^ 4 := fun hc => hVe
        (le_antisymm (by
          have := Subgroup.eq_of_le_of_card_ge hUV' (by rw [hc, card_refSub hv16])
          exact this.symm.le) hUV')
      have h32 : Nat.card V' = 2 ^ 5 := by
        obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
        rw [hk'] at hge hne ⊢
        have : k ≤ 5 := hk
        have : 4 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hge
        interval_cases k
        · exact absurd rfl hne
        · rfl
      exact Subgroup.eq_of_le_of_card_ge hVp (by rw [h32, card_refSub hvV32p])
    have hVeq' : pb e V = uV32p := hVeq
    set e' := conjE e ⟨k16, wG_mem _⟩ with he'
    have hUV2 : img e' u32 ≤ V := by
      rw [img_conjE]
      show img e (u32.map (MulAut.conj k16).toMonoidHom) ≤ V
      rw [map_k16_u32, ← hVeq', img_pb]
    have hyP : k16⁻¹ * x16 * k16 ∈ ruP :=
      ruP.mul_mem (ruP.mul_mem (ruP.inv_mem (wG_mem _)) (wG_mem _)) (wG_mem _)
    have hyM : e' ⟨_, hyP⟩ ∈ L := by
      rw [conjE_apply]
      convert hx using 2
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hyN : k16⁻¹ * x16 * k16 ∈ Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060))) :=
      conj_mem_normalizer_of_map map_k16_u32 (hVeq ▸ hLN hxM)
    have hy5 : (⟨_, hyP⟩ : G₀) ^ 5 ^ 1 = 1 := by
      apply Subtype.ext
      simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      rw [show (k16⁻¹ * x16 * k16) ^ 5 = k16⁻¹ * x16 ^ 5 * k16 by
        rw [show k16⁻¹ * x16 * k16 = k16⁻¹ * x16 * k16⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv],
        ← orderOf_x16, pow_orderOf_eq_one]
      group
    have hy1 : (⟨_, hyP⟩ : G₀) ≠ 1 := by
      intro h1
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_one] at h2
      have : x16 = 1 := by
        have : x16 = k16 * (k16⁻¹ * x16 * k16) * k16⁻¹ := by group
        rw [this, h2]
        group
      have h3 := orderOf_x16
      rw [this, orderOf_one] at h3
      exact absurd h3 (by norm_num)
    exact false_vz h e' hUV2 hyM hyN ⟨1, hy5⟩ hy1

theorem false_w16 {L V MK : Subgroup A} (h : KConfig A L V MK) (e : G₀ ≃* A)
    (hUV : img e u16 ≤ V) {y : G₀} (hyM : e y ∈ L)
    (hyN : (y : Equiv.Perm (Fin 4060)) ∈ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060))))
    (hy : ∃ k : ℕ, y ^ 5 ^ k = 1) (hy1 : y ≠ 1) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨n, hnN, hxM⟩ := exists_conj_std e inf_le_left ⟨wG_mem _, x16_mem_normalizer⟩
    orderOf_x16 not_dvd_card_normalizer16 ⟨y.2, hyN⟩ hy hy1 hyM
  have hnN' : ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060)) ∈
      Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060))) := by
    have := (ruP ⊓ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060)))).inv_mem hnN
    simpa using this.2
  have e1 : u16.map (MulAut.conj ((n⁻¹ : G₀) : Equiv.Perm (Fin 4060))).toMonoidHom = u16 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN'
  exact false_w16_core h (conjE e n⁻¹) (by rw [img_conjE, e1]; exact hUV) hxM

end Five

section Sixty


theorem config_e64 {L V MK : Subgroup A} (h : KConfig A L V MK) (e : G₀ ≃* A)
    {U : Subgroup (Equiv.Perm (Fin 4060))} (hU : U ≤ ruP) (hUV : img e U ≤ V)
    (hCU : ruP ⊓ Subgroup.centralizer (U : Set (Equiv.Perm (Fin 4060))) ≤ u64) :
    V = img e u64 ∧ pCoreOf 2 L = img e u64 ∧ L = img e M64 ∧
      Subgroup.centralizer (V : Set A) = img e u64 := by
  set V' := pb e V with hV'
  set L' := pb e L with hL'
  have hVP : V' ≤ ruP := pb_le e V
  have hUV' : U ≤ V' := (le_iff_img_le e hU).mp hUV
  obtain ⟨hVab, -⟩ := pb_comm_sq h.elemAbelian e
  have h64ab : ∀ a ∈ u64, ∀ b ∈ u64, a * b = b * a := fun a ha b hb =>
    eSub_comm hv64 a b (by rwa [← refSub_eq]) (by rwa [← refSub_eq])
  have hV64 : V' ≤ u64 := fun v hv => hCU ⟨hVP hv,
    Subgroup.mem_centralizer_iff.mpr fun u hu => hVab u (hUV' hu) v hv⟩
  have hC : ruP ⊓ Subgroup.centralizer (V' : Set (Equiv.Perm (Fin 4060))) = u64 := by
    refine le_antisymm (fun c hc => hCU ⟨hc.1, Subgroup.centralizer_le hUV' hc.2⟩) ?_
    refine le_inf (refSub_le_ruP _) fun x hx => Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    exact h64ab v (hV64 hv) x hx
  have hCA : Subgroup.centralizer (V : Set A) = img e u64 := by
    conv_lhs => rw [← img_pb e V]
    rw [centralizer_img e hVP, hC]
  have hK2 : IsPGroup 2 ↥(img e u64) := by
    rw [img]
    refine IsPGroup.map ?_ _
    refine IsPGroup.of_card (n := 6) ?_
    rw [card_subgroupOf_of_le (refSub_le_ruP _), card_refSub hv64]
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) := by rw [hCA]; exact hK2
  have hLN : L' ≤ ruP ⊓ Subgroup.normalizer (u64 : Set (Equiv.Perm (Fin 4060))) := by
    rw [← img_le_iff_le_pb, ← normalizer_img e (refSub_le_ruP _), ← hCA]
    exact h.le_normalizer_centralizer
  have hLperf : ⁅L', L'⁆ = L' := pb_perfect e h.perfect
  have hL64 : L' ≤ M64 := perf_N64 L' hLN hLperf
  have hM64N : M64 ≤ Subgroup.normalizer (L' : Set (Equiv.Perm (Fin 4060))) := by
    have h1 : img e M64 ≤ Subgroup.normalizer (L : Set A) := by
      refine le_trans ?_ (h.normalizer_centralizer_le hC2)
      rw [hCA, normalizer_img e (refSub_le_ruP _), img_le_img_iff e M64_le_ruP]
      exact le_inf M64_le_ruP M64_le_normalizer
    rw [le_iff_img_le e M64_le_ruP, pb_normalizer] at h1
    exact h1.trans inf_le_right
  have hVne : V' ≠ ⊥ := pb_ne_bot e h.ne_bot
  have hVL : V' ≤ L' := pb_mono e (h.le_pCoreOf.trans (pCoreOf_le 2 L))
  have hsup : L' ⊔ u64 = M64 := by
    have := simple_M64
    rcases forall_eq_of_simple this (L' ⊔ u64) le_sup_right (sup_le hL64 u64_le_M64)
      (fun m hm => CFSG.Quasithin.KGC31.Ru.mem_normalizer_sup (hM64N hm)
        (M64_le_normalizer hm)) with hs | hs
    · exfalso
      have hle : L' ≤ u64 := hs ▸ le_sup_left
      have hb : L' = ⊥ := by
        rw [← hLperf, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => h64ab y (hle hy) x (hle hx)
      exact hVne (le_bot_iff.mp (hb ▸ hVL))
    · exact hs
  have hinf : L' ⊓ u64 = u64 := by
    refine eq_of_M64_normal inf_le_right ?_ ?_
    · rw [← hsup]
      refine sup_le (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm)
        (M64_le_normalizer (hL64 hm))) fun u hu => mem_normalizer_inf (hM64N (u64_le_M64 hu))
          (Subgroup.le_normalizer hu)
    · intro hb
      apply hVne
      exact le_bot_iff.mp (hb ▸ le_inf hVL hV64)
  have hLeq : L' = M64 := by
    rw [← hsup]
    exact (sup_eq_left.mpr (hinf ▸ inf_le_left)).symm
  have hVeq : V' = u64 := by
    refine eq_of_M64_normal hV64 ?_ hVne
    rw [← hLeq]
    exact pb_le_normalizer e h.le_normalizer
  have hVA : V = img e u64 := (pb_eq_iff e (refSub_le_ruP _)).mpr hVeq
  exact ⟨hVA, le_antisymm (h.pCoreOf_le.trans hCA.le) (hVA ▸ h.le_pCoreOf),
    (pb_eq_iff e M64_le_ruP).mpr hLeq, hCA⟩

end Sixty

section Seven


theorem config_e {L V MK : Subgroup A} (h : KConfig A L V MK) (e : G₀ ≃* A)
    (hEV : img e uE ≤ V) (hxE : e ⟨xE, ruN_le xE_memN⟩ ∈ L) :
    V = img e uE ∧ IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) := by
  set V' := pb e V with hV'
  set L' := pb e L with hL'
  have hVP : V' ≤ ruP := pb_le e V
  have hEV' : uE ≤ V' := (le_iff_img_le e (refSub_le_ruP _)).mp hEV
  obtain ⟨hVab, hVsq⟩ := pb_comm_sq h.elemAbelian e
  have hLN : L' ≤ Subgroup.normalizer (V' : Set (Equiv.Perm (Fin 4060))) :=
    pb_le_normalizer e h.le_normalizer
  have hxM : xE ∈ L' := (apply_mem_iff_mem_pb e).mp hxE
  have hV32 : V' ≤ uV32E := by
    intro v hv
    refine mem_V32E_of (hVP hv) (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      hVab u (hEV' hu) v hv) (hVsq v hv) fun j _ => ?_
    have hc : xE ^ (j + 1) * v * (xE ^ (j + 1))⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hLN hxM) _) v).mp hv
    exact hVab v hv _ hc
  have hLE : L' ≤ ruN := by
    intro m hm
    rw [← ruN_eq_normalizer_E, ← uE_eq]
    refine ⟨pb_le e L hm, mem_normalizer_of_conj_le fun u hu => ?_⟩
    by_cases hu1 : u = 1
    · rw [hu1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    by_contra hn
    have h1 : m * u * m⁻¹ ∈ V' :=
      (Subgroup.mem_normalizer_iff.mp (hLN hm) u).mp (hEV' hu)
    have h2 := ncard_fixSet_of_mem_uV32E (hV32 h1) hn
    rw [ncard_fixSet_conj, ncard_fixSet_of_mem_uE hu hu1] at h2
    exact absurd h2 (by norm_num)
  have hCK : pb e (Subgroup.centralizer (V : Set A)) ≤ ruK := by
    rw [pb_centralizer, ← ruP_centralizer_E, ← uE_eq]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hEV')
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) :=
    isPGroup_of_pb e (isPGroup_ruK.to_le hCK)
  have hKV : img e ruK ≤ Subgroup.normalizer (V : Set A) := by
    rw [le_iff_img_le e ruK_le, pb_normalizer]
    refine le_inf ruK_le fun k hk => mem_normalizer_of_conj_le fun v hv => ?_
    have hvK : v ∈ ruK := uV32E_le_ruK (hV32 hv)
    have hc := commut_memE hk hvK
    rw [← uE_eq] at hc
    have : k * v * k⁻¹ = (k * v * k⁻¹ * v⁻¹) * v := by group
    rw [this]
    exact V'.mul_mem (hEV' hc) hv
  have hKL : img e ruK ≤ Subgroup.normalizer (L : Set A) :=
    hKV.trans ((CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V).trans
      (h.normalizer_centralizer_le hC2))
  have hLE' : L ≤ img e ruN := (img_le_iff_le_pb e).mpr hLE
  have hLK : L ≤ Subgroup.normalizer ((img e ruK : Subgroup A) : Set A) := by
    refine hLE'.trans ?_
    rw [normalizer_img e ruK_le, img_le_img_iff e ruN_le]
    exact le_inf ruN_le ruN_le_normalizer_K
  have hK2 : IsPGroup 2 ↥(img e ruK) := by
    rw [img]
    exact (isPGroup_ruK.of_equiv (Subgroup.subgroupOfEquivOfLe ruK_le).symm).map _
  have hKO : L ⊓ img e ruK ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm) (hLK hm))
      (hK2.to_le inf_le_right)
  set k := ruKGens.getD 0 1 with hk
  have hkK : k ∈ ruK := ruKGens_getD_mem 0
  have hkN : k ∈ Subgroup.normalizer (L' : Set (Equiv.Perm (Fin 4060))) := by
    have h1 := hKL
    rw [le_iff_img_le e ruK_le, pb_normalizer] at h1
    exact (h1 hkK).2
  have hcL : k * xE * k⁻¹ * xE⁻¹ ∈ L' := by
    have h1 : k * xE * k⁻¹ ∈ L' := (Subgroup.mem_normalizer_iff.mp hkN xE).mp hxM
    exact L'.mul_mem h1 (L'.inv_mem hxM)
  have hcK : k * xE * k⁻¹ * xE⁻¹ ∈ ruK := by
    have h1 : xE * k⁻¹ * xE⁻¹ ∈ ruK :=
      (Subgroup.mem_normalizer_iff.mp (ruN_le_normalizer_K xE_memN) k⁻¹).mp (ruK.inv_mem hkK)
    have : k * xE * k⁻¹ * xE⁻¹ = k * (xE * k⁻¹ * xE⁻¹) := by group
    rw [this]
    exact ruK.mul_mem hkK h1
  have hmem : e ⟨_, ruK_le hcK⟩ ∈ L ⊓ img e ruK :=
    ⟨(apply_mem_iff_mem_pb e).mpr hcL, (apply_mem_img e).mpr hcK⟩
  have hcC := h.pCoreOf_le (hKO hmem)
  rw [apply_mem_iff_mem_pb e, pb_centralizer] at hcC
  have hrep := rep_commutA (rep_ruKGens 0 (by norm_num)) rep_xE
  have hchk : (spV32E.all fun v => !commA v (commutA ruKGensA[0]! xEA) || inA spE v) = true :=
    Certificates.certificate725102
  have hVE : V' ≤ uE := by
    intro v hv
    obtain ⟨t, ht, htv⟩ := exists_rep_of_mem_refSub hbV32E hvV32E (hV32 hv)
    have h1 := List.all_eq_true.mp hchk t ht
    have hcomm : commA t (commutA ruKGensA[0]! xEA) = true :=
      (commA_iff htv hrep).mpr (Subgroup.mem_centralizer_iff.mp hcC.2 v hv)
    rw [hcomm, Bool.not_true, Bool.false_or] at h1
    exact mem_refSub_of_inA hbE hvE htv h1
  exact ⟨(pb_eq_iff e (refSub_le_ruP _)).mpr (le_antisymm hVE hEV'), hC2⟩

end Seven

end CFSG.SectionRank.QTK.Insp443.Ru

end
