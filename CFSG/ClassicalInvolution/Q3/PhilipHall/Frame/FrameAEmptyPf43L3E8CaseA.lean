module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43L3E8Clash
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartOne

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ComponentClassification.AschbacherTightEmbedding

namespace L3E8Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H Q E S : Subgroup T}

theorem normalizer_Q_le (cfg : L3E8Cfg K z J zJ H Q E S) :
    Subgroup.normalizer (Q : Set T) ≤
      sigmaNorm K ⊓ Subgroup.normalizer (firstFactor K : Set T) := by
  have hz := cfg.datum.unique
  have hzQ : z ∈ Q := cfg.E_le_Q cfg.z_mem_E
  intro y hy
  have hyz : y * z * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hy z).mp hzQ
  have h2 : (y * z * y⁻¹) * (y * z * y⁻¹) = 1 := by
    calc (y * z * y⁻¹) * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have h1 : y * z * y⁻¹ ≠ 1 := fun h => hz.ne_one (by
    have := congrArg (fun w => y⁻¹ * w * y) h
    simpa [mul_assoc] using this)
  obtain ⟨l, hl, hly⟩ := cfg.Q_conj cfg.efacts hyz h2 h1
  have hcz : l * y ∈ Subgroup.centralizer ({z} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * y * z = l * (y * z * y⁻¹) * y := by group
      _ = l * (l⁻¹ * z * l) * y := by rw [hly]
      _ = z * (l * y) := by group
  have e : y = l⁻¹ * (l * y) := by group
  rw [e]
  refine Subgroup.mem_inf.mpr ⟨(sigmaNorm K).mul_mem ((sigmaNorm K).inv_mem (cfg.ht_le_sigmaNorm hl))
    (cfg.cz_le hcz), ?_⟩
  exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hl))
    (cfg.cz_le_normalizer_ht hcz)

theorem normalizer_ht_le (cfg : L3E8Cfg K z J zJ H Q E S) :
    Subgroup.normalizer (firstFactor K : Set T) ≤ Subgroup.normalizer (Q : Set T) := by
  rw [cfg.hQ]
  exact normalizer_le_normalizer_oddTwoCoreIn _

theorem inv_Qconj (cfg : L3E8Cfg K z J zJ H Q E S) {x : T} (hx : x ∉ sigmaNorm K) {f : T}
    (hf : f ∈ rightConjugate Q x) (hf2 : f * f = 1) (hf1 : f ≠ 1) :
    ∃ w : T, w ∉ sigmaNorm K ∧ f = w⁻¹ * z * w := by
  have hf' : x * f * x⁻¹ ∈ Q := (mem_rightConjugate_iff Q x f).mp hf
  have h2 : (x * f * x⁻¹) * (x * f * x⁻¹) = 1 := by
    calc (x * f * x⁻¹) * (x * f * x⁻¹) = x * (f * f) * x⁻¹ := by group
      _ = 1 := by rw [hf2]; group
  have h1 : x * f * x⁻¹ ≠ 1 := fun h => hf1 (by
    have := congrArg (fun w => x⁻¹ * w * x) h
    simpa [mul_assoc] using this)
  obtain ⟨l, hl, hlf⟩ := cfg.Q_conj cfg.efacts hf' h2 h1
  refine ⟨l * x, fun hw => hx ?_, ?_⟩
  · have := (sigmaNorm K).mul_mem ((sigmaNorm K).inv_mem (cfg.ht_le_sigmaNorm hl)) hw
    simpa using this
  · calc f = x⁻¹ * (x * f * x⁻¹) * x := by group
      _ = x⁻¹ * (l⁻¹ * z * l) * x := by rw [hlf]
      _ = (l * x)⁻¹ * z * (l * x) := by group

private theorem caseA_isSylowOf {V P : Subgroup T} (h : IsSylow2In V P) :
    CFSG.ABGLocalTools.IsSylowOf 2 V P :=
  ⟨AscQuot.sylowOfIsSylow2In' h, by
    show (V.subgroupOf P).map P.subtype = V
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.1]⟩

private theorem caseA_comm {F : Subgroup T} (hF : IsElemAbelian 2 F) {a b : T} (ha : a ∈ F)
    (hb : b ∈ F) : a * b = b * a := by
  have := hF.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

private theorem caseA_isElemAbelian {F U : Subgroup T} (hF : IsElemAbelian 2 F) {g : T}
    (hU : U ≤ rightConjugate F g) : IsElemAbelian 2 U := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
  · have ha := (mem_rightConjugate_iff F g _).mp (hU a.2)
    have hb := (mem_rightConjugate_iff F g _).mp (hU b.2)
    have h := caseA_comm hF ha hb
    have h' : g * ((a : T) * b) * g⁻¹ = g * ((b : T) * a) * g⁻¹ := by
      calc g * ((a : T) * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
        _ = g * ((b : T) * a) * g⁻¹ := by group
    simpa using mul_left_cancel (mul_right_cancel h')
  · have h := hF.2 _ ((mem_rightConjugate_iff F g y).mp (hU hy))
    rw [conj_pow, conj_eq_one_iff] at h
    exact h

theorem card_T_ge_four (cfg : L3E8Cfg K z J zJ H Q E S) {x : T} (hx : x ∉ sigmaNorm K)
    {T₀ : Subgroup T}
    (hT : IsSylow2In T₀ (rightConjugate Q x ⊓ Subgroup.normalizer (Q : Set T))) (hT1 : T₀ ≠ ⊥) :
    4 ≤ Nat.card T₀ := by
  have hxN : x ∉ Subgroup.normalizer (Q : Set T) := fun h =>
    hx (Subgroup.mem_inf.mp (cfg.normalizer_Q_le h)).1
  have htight := cfg.tight
  have hodd : Odd (Nat.card (Q ⊓ rightConjugate Q x : Subgroup T)) := htight.2 x hxN
  have hfac : (Nat.card Q).factorization 2 = (Nat.card (rightConjugate Q x)).factorization 2 := by
    rw [rightConjugate_card]
  have hT2 : IsPGroup 2 T₀ := hT.2.1
  have hTN : T₀ ≤ Subgroup.normalizer (Q : Set T) := hT.1.trans inf_le_right
  obtain ⟨syl, hsyl⟩ := CFSG.ComponentClassification.TwoActionInvariantSylow.subgroup Q T₀ hT2 hTN
  set R : Subgroup T := (syl : Subgroup Q).map Q.subtype with hRdef
  have hR : CFSG.ABGLocalTools.IsSylowOf 2 R Q := ⟨syl, rfl⟩
  have hcard : Nat.card (R ⊓ Subgroup.normalizer (T₀ : Set T) : Subgroup T) = Nat.card T₀ :=
    CFSG.ComponentClassification.Asc76.Lemma22.card_inf_normalizer htight
      (rightConjugate_tightlyEmbedded Q htight x) hodd hfac (caseA_isSylowOf hT) hT1 hR hsyl
  have hR8 : Nat.card R = 8 := by
    rw [hR.card_eq, ← (caseA_isSylowOf cfg.E_sylow).card_eq, cfg.E8.2]
  obtain ⟨c, -, hc⟩ :=
    Disconnected.AschTight.Sec7.exists_conj_le_of_isSylow2In cfg.E_sylow hR.isPGroup hR.le
  have hRE : R ≤ rightConjugate E c⁻¹ := fun y hy => by
    rw [mem_rightConjugate_iff, inv_inv]
    exact mem_conjSub_iff.mp (hc hy)
  have hRab : IsElemAbelian 2 R := caseA_isElemAbelian cfg.E8.1 hRE
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb => caseA_comm hRab ha hb
  have hRsq : ∀ a ∈ R, a * a = 1 := fun a ha => by rw [← pow_two]; exact hRab.2 a ha
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have hT02 : Nat.card T₀ = 2 := by
    have h1 : Nat.card T₀ ≠ 1 := fun h => hT1 (Subgroup.card_eq_one.mp h)
    rcases n with _ | _ | n
    · exact absurd (by rw [hn, pow_zero]) h1
    · rw [hn, pow_one]
    · exfalso
      have : 4 ≤ Nat.card T₀ := by
        rw [hn]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2 : u * u = 1 := by
    have h := Subgroup.orderOf_dvd_natCard T₀ hu
    rw [hT02] at h
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1'
  have hTu : T₀ = Subgroup.zpowers u := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu)
    rw [Nat.card_zpowers, hord, hT02]
  have hCN : ∀ r : T, u * r * u⁻¹ = r → r ∈ Subgroup.normalizer (T₀ : Set T) := by
    intro r hr
    have hc : Commute u r := by
      show u * r = r * u
      calc u * r = u * r * u⁻¹ * u := by group
        _ = r * u := by rw [hr]
    rw [hTu]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact (hc.zpow_left k).eq
  have huR : ∀ r ∈ R, u * r * u⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hsyl hu) r).mp hr
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  let φ : ↥R →* ↥R :=
    { toFun := fun r => ⟨(r : T)⁻¹ * (u * r * u⁻¹), R.mul_mem (R.inv_mem r.2) (huR r r.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show ((a : T) * b)⁻¹ * (u * ((a : T) * b) * u⁻¹) =
          ((a : T)⁻¹ * (u * a * u⁻¹)) * ((b : T)⁻¹ * (u * b * u⁻¹))
        have h := hRcomm _ (R.inv_mem b.2) _ (R.mul_mem (R.inv_mem a.2) (huR a a.2))
        calc ((a : T) * b)⁻¹ * (u * ((a : T) * b) * u⁻¹)
            = (b : T)⁻¹ * ((a : T)⁻¹ * (u * a * u⁻¹)) * (u * b * u⁻¹) := by group
          _ = ((a : T)⁻¹ * (u * a * u⁻¹)) * (b : T)⁻¹ * (u * b * u⁻¹) := by rw [h]
          _ = ((a : T)⁻¹ * (u * a * u⁻¹)) * ((b : T)⁻¹ * (u * b * u⁻¹)) := by group) }
  have hker : φ.ker.map R.subtype ≤ R ⊓ Subgroup.normalizer (T₀ : Set T) := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨r.2, hCN r ?_⟩
    have h1 : ((φ r : ↥R) : T) = 1 := by rw [MonoidHom.mem_ker.mp hr]; rfl
    change (r : T)⁻¹ * (u * r * u⁻¹) = 1 at h1
    exact (inv_mul_eq_one.mp h1).symm
  have hrange : φ.range.map R.subtype ≤ R ⊓ Subgroup.normalizer (T₀ : Set T) := by
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    refine ⟨(φ r).2, hCN _ ?_⟩
    show u * ((r : T)⁻¹ * (u * r * u⁻¹)) * u⁻¹ = (r : T)⁻¹ * (u * r * u⁻¹)
    have ha : u * (r : T) * u⁻¹ ∈ R := huR r r.2
    have e0 : u * (r : T) * u⁻¹ = u⁻¹ * r * u := by rw [hu_inv]
    calc u * ((r : T)⁻¹ * (u * r * u⁻¹)) * u⁻¹ = u * ((r : T)⁻¹ * (u⁻¹ * r * u)) * u⁻¹ := by
          rw [e0]
      _ = (u * r * u⁻¹)⁻¹ * r := by group
      _ = (u * r * u⁻¹) * r := by rw [inv_eq_of_mul_eq_one_right (hRsq _ ha)]
      _ = r * (u * r * u⁻¹) := hRcomm _ ha _ r.2
      _ = (r : T)⁻¹ * (u * r * u⁻¹) := by rw [inv_eq_of_mul_eq_one_right (hRsq _ r.2)]
  have h1 : Nat.card φ.ker ≤ 2 :=
    calc Nat.card φ.ker = Nat.card (φ.ker.map R.subtype) :=
          (Subgroup.card_map_of_injective R.subtype_injective).symm
      _ ≤ Nat.card (R ⊓ Subgroup.normalizer (T₀ : Set T) : Subgroup T) := Subgroup.card_le_of_le hker
      _ = 2 := by rw [hcard, hT02]
  have h2 : Nat.card φ.range ≤ 2 :=
    calc Nat.card φ.range = Nat.card (φ.range.map R.subtype) :=
          (Subgroup.card_map_of_injective R.subtype_injective).symm
      _ ≤ Nat.card (R ⊓ Subgroup.normalizer (T₀ : Set T) : Subgroup T) :=
          Subgroup.card_le_of_le hrange
      _ = 2 := by rw [hcard, hT02]
  have h3 := Subgroup.card_ker_mul_card_range φ
  rw [hR8] at h3
  have h4 : Nat.card φ.ker * Nat.card φ.range ≤ 2 * 2 := Nat.mul_le_mul h1 h2
  omega

theorem lemmaA (cfg : L3E8Cfg K z J zJ H Q E S) {x : T}
    (hx : x⁻¹ * z * x ∈ Subgroup.normalizer (Q : Set T)) : x ∈ sigmaNorm K := by
  by_contra hxM
  have hz := cfg.datum.unique
  have hzQ : z ∈ Q := cfg.E_le_Q cfg.z_mem_E
  have huQx : x⁻¹ * z * x ∈ rightConjugate Q x := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hzQ
  have hu2 : (x⁻¹ * z * x) * (x⁻¹ * z * x) = 1 := by
    calc (x⁻¹ * z * x) * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x := by group
      _ = 1 := by rw [hz.sq]; group
  have hu1 : x⁻¹ * z * x ≠ 1 := fun h => hz.ne_one (by
    have := congrArg (fun w => x * w * x⁻¹) h
    simpa [mul_assoc] using this)
  have hord : orderOf (x⁻¹ * z * x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hup : IsPGroup 2 (Subgroup.zpowers (x⁻¹ * z * x)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨T₀, hT₀, huT₀⟩ := IsSylow2In.exists_ge hup
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨huQx, hx⟩))
  have hT1 : T₀ ≠ ⊥ := fun h => hu1 (by
    have := huT₀ (Subgroup.mem_zpowers (x⁻¹ * z * x))
    rwa [h, Subgroup.mem_bot] at this)
  have h4 : 4 ≤ Nat.card T₀ := cfg.card_T_ge_four hxM hT₀ hT1
  have hT₀2 : IsPGroup 2 T₀ := hT₀.2.1
  have hT₀Qx : T₀ ≤ rightConjugate Q x := hT₀.1.trans inf_le_left
  have hXQ : conjSub x T₀ ≤ Q := fun y hy => by
    have h1 := (mem_rightConjugate_iff Q x _).mp (hT₀Qx (mem_conjSub_iff.mp hy))
    simpa [mul_assoc] using h1
  obtain ⟨c, hcQ, hc⟩ := Disconnected.AschTight.Sec7.exists_conj_le_of_isSylow2In cfg.E_sylow
    (isPGroup_conjSub x hT₀2) hXQ
  have hT₀E : T₀ ≤ rightConjugate E (c⁻¹ * x) := fun t ht => by
    rw [mem_rightConjugate_iff]
    have h1 := mem_conjSub_iff.mp (hc (conj_mem_conjSub (n := x) ht))
    convert h1 using 1
    group
  obtain ⟨n, hn⟩ := hT₀2.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ 2 ∣ Nat.card T₀ := by
    rw [hn]
    exact pow_dvd_pow 2 hn2
  obtain ⟨U₀, hU₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have hUT₀ : U₀.map T₀.subtype ≤ T₀ := Subgroup.map_subtype_le _
  have hU4 : Nat.card (U₀.map T₀.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective T₀.subtype_injective, hU₀]
    norm_num
  have hUE : U₀.map T₀.subtype ≤ rightConjugate E (c⁻¹ * x) := hUT₀.trans hT₀E
  have hUab : IsElemAbelian 2 (U₀.map T₀.subtype) := caseA_isElemAbelian cfg.E8.1 hUE
  have hUN : U₀.map T₀.subtype ≤ Subgroup.normalizer (firstFactor K : Set T) := fun y hy =>
    (Subgroup.mem_inf.mp (cfg.normalizer_Q_le (Subgroup.mem_inf.mp (hT₀.1 (hUT₀ hy))).2)).2
  have hcx : c⁻¹ * x ∈ sigmaNorm K := l3e8_clash cfg hUab hU4 hUN hUE
  apply hxM
  have hc' : c ∈ sigmaNorm K := cfg.ht_le_sigmaNorm (cfg.Q_le_ht hcQ)
  simpa using (sigmaNorm K).mul_mem hc' hcx

theorem zconj_cent (cfg : L3E8Cfg K z J zJ H Q E S) {x : T}
    (hx : x⁻¹ * z * x ∈ Subgroup.centralizer ({z} : Set T)) : x ∈ sigmaNorm K :=
  cfg.lemmaA (cfg.normalizer_ht_le (cfg.cz_le_normalizer_ht hx))

theorem lemmaA_conj (cfg : L3E8Cfg K z J zJ H Q E S) {m g : T} (hm : m ∈ sigmaNorm K)
    (hg : g ∉ sigmaNorm K) :
    m⁻¹ * z * m ∉ Subgroup.normalizer (rightConjugate (firstFactor K) g : Set T) := by
  intro hN
  have h1 : g * (m⁻¹ * z * m) * g⁻¹ ∈ Subgroup.normalizer (firstFactor K : Set T) := by
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro w
    have := hN (g⁻¹ * w * g)
    simp only [SetLike.mem_coe, mem_rightConjugate_iff] at this ⊢
    rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group,
      show g * (m⁻¹ * z * m * (g⁻¹ * w * g) * (m⁻¹ * z * m)⁻¹) * g⁻¹ =
        g * (m⁻¹ * z * m) * g⁻¹ * w * (g * (m⁻¹ * z * m) * g⁻¹)⁻¹ by group] at this
    exact this
  have h2 := cfg.normalizer_ht_le h1
  have e : g * (m⁻¹ * z * m) * g⁻¹ = (m * g⁻¹)⁻¹ * z * (m * g⁻¹) := by group
  rw [e] at h2
  have h3 := cfg.lemmaA h2
  apply hg
  have := (sigmaNorm K).mul_mem ((sigmaNorm K).inv_mem h3) hm
  simpa using this

end L3E8Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
