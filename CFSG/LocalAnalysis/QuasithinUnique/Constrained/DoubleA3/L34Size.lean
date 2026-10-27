module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Struct

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped MatrixGroups

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem normalizer_le_of_eight (hcard : Nat.card Y = 168)
    (hcent : ∀ a : Y, a ≠ 1 → a * a = 1 → IsPGroup 2 ↥(Subgroup.centralizer ({a} : Set Y)))
    {P : Subgroup Y} (hP8 : Nat.card P = 8) (hnab : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) :
    normalizer (P : Set Y) ≤ P := by
  have hZ : Nat.card (Subgroup.center ↥P) = 2 := by
    obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow (p := 2) (n := 3)
      (by rw [hP8]; norm_num) (by norm_num)
    have hdvd : 2 ^ k ∣ 2 ^ 3 := by
      rw [← hk, show (2 : ℕ) ^ 3 = Nat.card ↥P by rw [hP8]; norm_num]
      exact Subgroup.card_subgroup_dvd_card _
    have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    interval_cases k
    · simpa using hk
    · exfalso
      have hq : Nat.card (↥P ⧸ Subgroup.center ↥P) = 2 := by
        have := (Subgroup.center ↥P).card_mul_index
        rw [hk, hP8] at this
        rw [← Subgroup.index_eq_card]
        omega
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsCyclic (↥P ⧸ Subgroup.center ↥P) := isCyclic_of_prime_card hq
      have hab := (QuotientGroup.mk' (Subgroup.center ↥P)).isMulCommutative_of_isCyclic_of_ker_le_center
        (by rw [QuotientGroup.ker_mk'])
      obtain ⟨a, ha, b, hb, hab'⟩ := hnab
      exact hab' (congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    · exfalso
      have hcomm : IsMulCommutative ↥P := Subgroup.center_eq_top_iff.mp (by
        apply Subgroup.eq_top_of_card_eq
        rw [hk, hP8]; norm_num)
      obtain ⟨a, ha, b, hb, hab'⟩ := hnab
      exact hab' (congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  obtain ⟨y, hy1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(Subgroup.center ↥P))).mp hZ
  have hzP : ((y : ↥P) : Y) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  have hzsq : ((y : ↥P) : Y) * ((y : ↥P) : Y) = 1 := by
    have h1 : orderOf y ∣ 2 := hZ ▸ orderOf_dvd_natCard y
    have h2 : y ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    have h3 : (y : ↥P) * (y : ↥P) = 1 := by
      have := congrArg Subtype.val h2
      simpa [pow_two] using this
    simpa using congrArg Subtype.val h3
  have hzc : ∀ p ∈ P, p * ((y : ↥P) : Y) = ((y : ↥P) : Y) * p := fun p hp => by
    have := Subgroup.mem_center_iff.mp y.2 ⟨p, hp⟩
    exact congrArg Subtype.val this
  intro n hn
  set z : Y := ((y : ↥P) : Y) with hzdef
  have hnz : n * z * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn z).mp (y : ↥P).2
  have hw : (⟨n * z * n⁻¹, hnz⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    show (q : Y) * (n * z * n⁻¹) = n * z * n⁻¹ * (q : Y)
    have hq : n⁻¹ * (q : Y) * n ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer (P : Set Y)).inv_mem hn) (q : Y)).mp q.2
      simpa using this
    have h1 := hzc _ hq
    calc (q : Y) * (n * z * n⁻¹) = n * ((n⁻¹ * (q : Y) * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * (q : Y) * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * (q : Y) := by group
  have hw1 : (⟨⟨n * z * n⁻¹, hnz⟩, hw⟩ : ↥(Subgroup.center ↥P)) ≠ 1 := by
    intro h
    apply hzP
    have h' : n * z * n⁻¹ = 1 := congrArg (fun t : ↥(Subgroup.center ↥P) => ((t : ↥P) : Y)) h
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h']; group
  have hnzz : n * z * n⁻¹ = z := by
    have := huniq _ hw1
    exact congrArg (fun t : ↥(Subgroup.center ↥P) => ((t : ↥P) : Y)) this
  have hnC : n ∈ Subgroup.centralizer ({z} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [hnzz]
  have hCc : IsPGroup 2 ↥(Subgroup.centralizer ({z} : Set Y)) := hcent z hzP hzsq
  have hPle : P ≤ Subgroup.centralizer ({z} : Set Y) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc p hp)
  have hCle : Nat.card ↥(Subgroup.centralizer ({z} : Set Y)) ≤ 8 := by
    obtain ⟨k, hk⟩ := hCc.exists_card_eq
    have hd : 2 ^ k ∣ 8 * 21 := by
      have := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({z} : Set Y))
      rw [hk, hcard] at this
      simpa using this
    have h8 : 2 ^ k ∣ 8 :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 21)) hd
    rw [hk]
    exact Nat.le_of_dvd (by norm_num) h8
  have hPC : P = Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.eq_of_le_of_card_ge hPle (hP8 ▸ hCle)
  rw [hPC]
  exact hnC

theorem not_inner_of_moves_normal (hcard : Nat.card Y = 168)
    (hcent : ∀ a : Y, a ≠ 1 → a * a = 1 → IsPGroup 2 ↥(Subgroup.centralizer ({a} : Set Y)))
    {P V : Subgroup Y} (hP8 : Nat.card P = 8) (hnab : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a)
    (hVn : P ≤ normalizer (V : Set Y)) (α : MulAut Y) (hαP : ∀ y ∈ P, α y ∈ P)
    (hαV : ∃ v ∈ V, α v ∉ V) : ¬ ∃ k : Y, ∀ y, α y = k * y * k⁻¹ := by
  rintro ⟨k, hk⟩
  have hkP : k ∈ normalizer (P : Set Y) := by
    apply mem_normalizer_of_conj_mem
    intro a ha
    rw [← hk]
    exact hαP a ha
  have hkP' : k ∈ P := normalizer_le_of_eight hcard hcent hP8 hnab hkP
  obtain ⟨v, hv, hαv⟩ := hαV
  apply hαv
  rw [hk]
  exact (Subgroup.mem_normalizer_iff.mp (hVn hkP') v).mp hv

end Generic

section GenericG

variable {G : Type} [Group G] [Finite G]

theorem not_inner_conj {Y R V : Subgroup G} {x : G} (hd : L2pData ↥Y) (hcard : Nat.card Y = 168)
    (hRK8 : Nat.card ↥(R ⊓ Y) = 8) (hVY : V ≤ Y) (hVR : V ≤ R) (hRV : R ≤ normalizer (V : Set G))
    (hxY : x ∈ normalizer (Y : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnab : ¬ conjR V x ≤ Subgroup.centralizer (V : Set G)) (hne : conjR V x ≠ V) :
    ¬ ∃ k ∈ Y, ∀ y ∈ Y, x⁻¹ * y * x = k⁻¹ * y * k := by
  rintro ⟨k, hkY, hk⟩
  have hcent : ∀ a : ↥Y, a ≠ 1 → a * a = 1 →
      IsPGroup 2 ↥(Subgroup.centralizer ({a} : Set ↥Y)) := fun a ha1 ha2 =>
    hd.cent_two a (orderOf_eq_prime (by rwa [← pow_two] at ha2) ha1)
  obtain ⟨α, hα⟩ := exists_conjAut hxY
  set P : Subgroup ↥Y := (R ⊓ Y).subgroupOf Y with hPdef
  set V' : Subgroup ↥Y := V.subgroupOf Y with hVdef
  have hP8 : Nat.card P = 8 := by
    rw [hPdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ⊓ Y ≤ Y)).toEquiv]
    exact hRK8
  have hxRinv : ∀ y ∈ R, x⁻¹ * y * x ∈ R := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (R : Set G)).inv_mem hxR) y).mp hy
    simpa using this
  have hnab' : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply hnab
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hyx : x * y * x⁻¹ ∈ V := mem_conjR.mp hy
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    have hyY : y ∈ Y := by
      have h1 := (Subgroup.mem_normalizer_iff.mp ((normalizer (Y : Set G)).inv_mem hxY)
        (x * y * x⁻¹)).mp (hVY hyx)
      have h2 : x⁻¹ * (x * y * x⁻¹) * x ∈ Y := by simpa using h1
      rwa [e] at h2
    have hyR : y ∈ R := by
      have h2 := hxRinv _ (hVR hyx)
      rwa [e] at h2
    have h1 := hcon ⟨u, hVY hu⟩ (by rw [hPdef]; exact Subgroup.mem_subgroupOf.mpr ⟨hVR hu, hVY hu⟩)
      ⟨y, hyY⟩ (by rw [hPdef]; exact Subgroup.mem_subgroupOf.mpr ⟨hyR, hyY⟩)
    exact (congrArg Subtype.val h1)
  have hVn : P ≤ normalizer V' := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have hrR : (r : G) ∈ R := ((Subgroup.mem_subgroupOf.mp hr) : (r : G) ∈ R ⊓ Y).1
    have := Subgroup.mem_normalizer_iff.mp (hRV hrR) (v : G)
    show (v : G) ∈ V ↔ ((r * v * r⁻¹ : ↥Y) : G) ∈ V
    exact this
  have hαP : ∀ y ∈ P, α y ∈ P := by
    intro y hy
    have hy' : (y : G) ∈ R ⊓ Y := Subgroup.mem_subgroupOf.mp hy
    have hR' : x⁻¹ * (y : G) * x ∈ R := hxRinv _ hy'.1
    rw [hPdef, Subgroup.mem_subgroupOf, hα]
    exact ⟨hR', (α y).2 |> fun h => by rw [hα] at h; exact h⟩
  have hαV : ∃ v ∈ V', α v ∉ V' := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hle : conjR V x ≤ V := by
      intro w hw
      have hv : x * w * x⁻¹ ∈ V := mem_conjR.mp hw
      have hvY : x * w * x⁻¹ ∈ Y := hVY hv
      have h1 := hcon ⟨x * w * x⁻¹, hvY⟩ (Subgroup.mem_subgroupOf.mpr hv)
      rw [hVdef, Subgroup.mem_subgroupOf, hα] at h1
      have e : x⁻¹ * (x * w * x⁻¹) * x = w := by group
      rw [e] at h1
      exact h1
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjR])
  refine not_inner_of_moves_normal hcard hcent hP8 hnab' hVn α hαP hαV ⟨⟨k⁻¹, Y.inv_mem hkY⟩, fun y => ?_⟩
  apply Subtype.ext
  rw [hα]
  show x⁻¹ * (y : G) * x = (k⁻¹ : G) * (y : G) * ((k⁻¹)⁻¹ : G)
  rw [inv_inv]
  exact hk y y.2

end GenericG

section Main

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem card_psl27 : Nat.card PSL(2, ZMod 7) = 168 := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hF : ringChar (ZMod 7) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; norm_num
  have h5 : 5 ≤ Fintype.card (ZMod 7) := by simp
  have h := CFSG.QuasithinUnique.K1.psl2_card_mul_two hF h5
  simp only [ZMod.card] at h
  have h' : Nat.card PSL(2, ZMod 7) * 2 = 336 := h.trans (by norm_num)
  omega

omit [Finite G] in
theorem A3A3K.blockU_ne_conjR_x [Finite G] (hK : A3A3K T M H S L s x z₁ z₂ K) :
    blockU L ≠ conjR (blockU L) x := by
  intro h
  apply hK.x_good
  rw [← h]
  intro u hu
  exact Subgroup.mem_centralizer_iff.mpr fun v hv => hK.isA4.comm_U v hv u hu

omit [Finite G] in
theorem A3A3K.blockU2_ne_conjR_x [Finite G] (hK : A3A3K T M H S L s x z₁ z₂ K) :
    blockU2 L s ≠ conjR (blockU2 L s) x := by
  intro h
  apply hK.x_good₂
  rw [← h]
  intro u hu
  exact Subgroup.mem_centralizer_iff.mpr fun v hv => hK.isA4s.comm_U v hv u hu

section Sizes

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hI : Inputs2436)
  (hK : A3A3K T M H S L s x z₁ z₂ K) (hc : blockU2 L s ≤ Subgroup.centralizer (K : Set G))
include hD h27_1 hI hK hc

theorem A3A3K.l2pData_K : L2pData ↥K := by
  obtain ⟨e⟩ := hK.nonempty_psl27 hD h27_1 hI hc
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hd : L2pData PSL(2, ZMod 7) :=
    Unc25K1.psl2_l2pData (K := ZMod 7) (p := 7) le_rfl (by simp)
      (Or.inr ⟨by norm_num, 3, by norm_num⟩)
  exact Unc25K1.l2pData_of_mulEquiv e hd

theorem A3A3K.card_K_eq
    : Nat.card K = 168 := by
  obtain ⟨e⟩ := hK.nonempty_psl27 hD h27_1 hI hc
  rw [Nat.card_congr e.toEquiv]
  exact card_psl27

theorem A3A3K.card_Ks_eq
    : Nat.card ↥(conjR K s) = 168 := by
  rw [card_conjR]
  exact hK.card_K_eq hD h27_1 hI hc

theorem A3A3K.l2pData_Ks
    : L2pData ↥(conjR K s) := by
  obtain ⟨ι, -⟩ := exists_conjR_equiv K s
  exact Unc25K1.l2pData_of_mulEquiv ι.symm (hK.l2pData_K hD h27_1 hI hc)

theorem A3A3K.card_sup_K_Ks
    : Nat.card ↥(K ⊔ conjR K s) = 168 * 168 := by
  have hN : K ≤ normalizer (conjR K s : Set G) :=
    C5.le_normalizer_of_commute (hK.comm_K_Ks hD h27_1 hI hc)
  have h := C5.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hK.inf_K_Ks hD h27_1 hI hc, Subgroup.card_bot, mul_one, hK.card_Ks_eq hD h27_1 hI hc,
    hK.card_K_eq hD h27_1 hI hc] at h
  exact h

theorem A3A3K.card_rK
    : Nat.card ↥(baum S ⊓ K) = 8 := by
  have hcs := hK.cs
  have hUx := hK.blockUx_le_rK hD h27_1
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hK.a3
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  have hbT : baum S ≤ T := (inf_le_left : baum S ≤ S).trans hcs.le_T
  have hle : blockU L ⊔ conjR (blockU L) x ≤ baum S ⊓ K := sup_le (le_inf hUB hUK) hUx
  have hpow : IsPGroup 2 ↥(baum S ⊓ K) := hcs.setting.isPGroup.to_le (inf_le_left.trans hbT)
  have h2 : IsPGroup 2 ↥(blockU L ⊔ conjR (blockU L) x) := hpow.to_le hle
  have h8 := eight_dvd_card_of_four hK.isA4.card_U (hK.isA4.conj x).card_U
    hK.blockU_ne_conjR_x h2
  have h8' : 8 ∣ Nat.card ↥(baum S ⊓ K) := h8.trans (Subgroup.card_dvd_of_le hle)
  obtain ⟨n, hn⟩ := hpow.exists_card_eq
  have hdvd : Nat.card ↥(baum S ⊓ K) ∣ 8 * 21 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : baum S ⊓ K ≤ K)
    rwa [hK.card_K_eq hD h27_1 hI hc] at this
  rw [hn] at h8' hdvd ⊢
  have h3 : 3 ≤ n := (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp
    (by simpa using h8' : 2 ^ 3 ∣ 2 ^ n)
  have h3' : n ≤ 3 := by
    have h8d : 2 ^ n ∣ 8 :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 21)) hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp
      (by simpa using h8d : 2 ^ n ∣ 2 ^ 3)
  have : n = 3 := le_antisymm h3' h3
  rw [this]; norm_num

theorem A3A3K.card_rKs
    : Nat.card ↥(baum S ⊓ conjR K s) = 8 := by
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hK.s_mem
  have h : conjR (baum S ⊓ K) s = baum S ⊓ conjR K s := by
    rw [Lin2.conjR_inf, mem_normalizer_iff_conjR_eq.mp hsB]
  rw [← h, card_conjR]
  exact hK.card_rK hD h27_1 hI hc

theorem A3A3K.x_not_inner
    : ¬ ∃ k ∈ K, ∀ y ∈ K, x⁻¹ * y * x = k⁻¹ * y * k := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hK.a3
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  exact not_inner_conj (hK.l2pData_K hD h27_1 hI hc) (hK.card_K_eq hD h27_1 hI hc)
    (hK.card_rK hD h27_1 hI hc) hUK hUB (baum_le_normalizer_blockU hcs hK.a3)
    hK.x_mem_normalizer_K (hK.toA3A3x.x_mem_normalizer_baum hB) hK.x_good
    hK.blockU_ne_conjR_x.symm

theorem A3A3K.x_not_inner_Ks
    : ¬ ∃ k ∈ conjR K s, ∀ y ∈ conjR K s, x⁻¹ * y * x = k⁻¹ * y * k := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hK.s_mem
  have hUK : blockU2 L s ≤ conjR K s := by
    intro y hy
    rw [blockU2, mem_conjR] at hy
    rw [mem_conjR]
    exact hK.isA4.le.trans hK.L_le_K hy
  have hUB : blockU2 L s ≤ baum S := by
    have h1 : blockU2 L s ≤ conjR (baum S) s :=
      Lin2.conjR_mono (blockU_le_baum hcs hK.a3) s
    rwa [mem_normalizer_iff_conjR_eq.mp hsB] at h1
  exact not_inner_conj (hK.l2pData_Ks hD h27_1 hI hc) (hK.card_Ks_eq hD h27_1 hI hc)
    (hK.card_rKs hD h27_1 hI hc) hUK hUB hK.baum_le_normalizer_blockU2
    (hK.x_mem_normalizer_Ks hD h27_1 hI hc) (hK.toA3A3x.x_mem_normalizer_baum hB) hK.x_good₂
    hK.blockU2_ne_conjR_x.symm

end Sizes

end Main

end CFSG.QuasithinUnique.DoubleA3
