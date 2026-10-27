module

public import CFSG.Goldschmidt.StatementsG
import CFSG.Goldschmidt.Steps.G36TypeI
import CFSG.Goldschmidt.Steps.G3aAut
import CFSG.Goldschmidt.Steps.LemmaXCore
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
import CFSG.Walter.Bender1970.S38.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.Goldschmidt

namespace G76

open CFSG.Open CFSG.ComponentClassification
open scoped Pointwise commutatorElement

section FixedPoints

variable {X : Type*} [Group X] [Finite X]

theorem card_modEq_card_inf_centralizer {p : ℕ} [hp : Fact p.Prime] {x : X} (hx : x ^ p = 1)
    {Y : Subgroup X} (hxY : x ∈ Subgroup.normalizer (Y : Set X)) :
    Nat.card Y ≡ Nat.card (Y ⊓ Subgroup.centralizer ({x} : Set X) : Subgroup X) [MOD p] := by
  classical
  set R := Subgroup.zpowers x with hR
  have hRY : R ≤ Subgroup.normalizer (Y : Set X) := Subgroup.zpowers_le.mpr hxY
  let := Subgroup.conjMulDistribMulActionOfLeNormalizer R Y hRY
  have hRp : IsPGroup p R := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp
      (orderOf_dvd_of_pow_eq_one (show x ^ p ^ 1 = 1 by rw [pow_one]; exact hx))
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hmod := hRp.card_modEq_card_fixedPoints Y
  have hsmul : ∀ (r : R) (y : Y), ((r • y : Y) : X) = (r : X) * y * (r : X)⁻¹ := fun r y =>
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit R Y hRY r y
  let e : MulAction.fixedPoints R Y ≃
      (Y ⊓ Subgroup.centralizer ({x} : Set X) : Subgroup X) :=
    { toFun := fun y => ⟨((y : Y) : X), Subgroup.mem_inf.mpr ⟨(y : Y).2, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := congrArg Subtype.val (y.2 ⟨x, Subgroup.mem_zpowers x⟩)
        rw [hsmul] at h1
        calc ((y : Y) : X) * x = x * (y : Y) * x⁻¹ * x := by rw [h1]
          _ = x * (y : Y) := by group⟩⟩
      invFun := fun z => ⟨⟨z, (Subgroup.mem_inf.mp z.2).1⟩, fun r => by
        apply Subtype.ext
        rw [hsmul]
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp r.2
        have hc : Commute x (z : X) :=
          (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp z.2).2).symm
        have hcj : Commute (x ^ j) (z : X) := hc.zpow_left j
        rw [← hj]
        change x ^ j * (z : X) * (x ^ j)⁻¹ = z
        rw [hcj.eq, mul_inv_cancel_right]⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }
  rwa [Nat.card_congr e] at hmod

end FixedPoints

section Center

variable {L : Type} [Group L] [Finite L]

theorem center_two_eq_one_of_psu3 (hLq : CFSG.Open.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* PSU3 2 2) :
    ∀ z ∈ Subgroup.center L, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center L with hZdef
  set O := goldschmidtOddCore L with hOdef
  have hOodd : Odd (Nat.card O) := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := L)
    rw [hOdef, goldschmidtOddCore_eq_pPrimeCore]
    exact Nat.coprime_two_left.mp this
  have hOZ : O ≤ Z := by
    rcases Quasisimple.normal_le_center_or_eq_top hLq O with hle | htop
    · exact hle
    · exfalso
      have h2 := LemmaX.two_dvd_card_of_isQuasisimple hLq
      rw [← Subgroup.card_top (G := L), ← htop] at h2
      exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2)
  set ψ := QuotientGroup.mk' O with hψdef
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective O
  have : Group.IsPerfect L := ⟨hLq.1⟩
  have hker : ψ.ker ≤ Z := by rw [QuotientGroup.ker_mk']; exact hOZ
  have hQ : CFSG.Open.IsQuasisimple (L ⧸ O) := Quasisimple.central_quotient hLq O hOZ
  have : Group.IsPerfect (L ⧸ O) := ⟨hQ.1⟩
  have hZQ' : Z.map ψ = Subgroup.center (L ⧸ O) :=
    Quasisimple.center_map_of_central_kernel ψ hψs hker
  let eQ : (L ⧸ O) ⧸ Subgroup.center (L ⧸ O) ≃* L ⧸ Z :=
    (QuotientGroup.congr (Z.map ψ) (Subgroup.center (L ⧸ O)) (MulEquiv.refl _)
      (by simpa using hZQ')).symm.trans (QuotientGroup.quotientQuotientEquivQuotient O Z hOZ)
  have hZQ2 : IsPGroup 2 (Subgroup.center (L ⧸ O)) := by
    rintro ⟨g, hg⟩
    rw [← hZQ'] at hg
    obtain ⟨z, hz, rfl⟩ := hg
    refine ⟨(orderOf z).factorization 2, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hψdef, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have hodd : Odd (orderOf (z ^ 2 ^ (orderOf z).factorization 2)) := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (Nat.ordProj_dvd _ _)]
      exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (orderOf_pos z).ne')
    have hnormal : (Subgroup.zpowers (z ^ 2 ^ (orderOf z).factorization 2)).Normal :=
      Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ hz _))
    have hle : Subgroup.zpowers (z ^ 2 ^ (orderOf z).factorization 2) ≤ O :=
      le_sSup ⟨hnormal, by rw [Nat.card_zpowers]; exact hodd⟩
    exact hle (Subgroup.mem_zpowers _)
  have hbot : Subgroup.center (L ⧸ O) = ⊥ :=
    CFSG.QuasithinUnique.RankOneRecog.unitary_center_eq_bot hZQ2 le_rfl (eQ.trans e)
  intro z hz k hk
  have hzQ : ψ z ∈ Subgroup.center (L ⧸ O) := hZQ' ▸ ⟨z, hz, rfl⟩
  rw [hbot, Subgroup.mem_bot, hψdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hzQ
  exact eq_one_of_pow_two_pow_eq_one hOodd hzQ hk

end Center

section Sylow

theorem card_map_eq_of_injOn {L M : Type*} [Group L] [Group M] (f : L →* M) {X : Subgroup L}
    (h : ∀ s ∈ X, ∀ t ∈ X, f s = f t → s = t) : Nat.card (X.map f) = Nat.card X := by
  rw [← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn h]
  rfl

theorem eq_four_or_eq_of_modEq {m : ℕ} (hdvd : m ∣ 64) (h4 : 4 ∣ m)
    (hmod : m ≡ 4 [MOD 5]) : m = 4 ∨ m = 64 := by
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show m ∣ 2 ^ 6 by norm_num; exact hdvd)
  interval_cases j <;> simp_all [Nat.ModEq]

theorem eq_four_of_modEq {m : ℕ} (hdvd : m ∣ 4) (hmod : 4 ≡ m [MOD 5]) : m = 4 := by
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases m <;> simp_all [Nat.ModEq]

variable {L : Type} [Group L] [Finite L]

theorem psu34_sylow_facts (h32 : S_G32) (hLq : CFSG.Open.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* PSU3 2 2)
    (hZ2 : ∀ z ∈ Subgroup.center L, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1) (P : Sylow 2 L) :
    Nat.card (P : Subgroup L) = 64 ∧
    Nat.card ((P : Subgroup L) ⊓ Subgroup.centralizer ((P : Subgroup L) : Set L) :
      Subgroup L) = 4 ∧
    ⁅(P : Subgroup L), (P : Subgroup L)⁆ =
      (P : Subgroup L) ⊓ Subgroup.centralizer ((P : Subgroup L) : Set L) ∧
    ((P : Subgroup L) ⊓ Subgroup.centralizer ((P : Subgroup L) : Set L)).map
        (QuotientGroup.mk' (Subgroup.center L)) =
      CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
        ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)) :
          Sylow 2 (L ⧸ Subgroup.center L)) : Subgroup (L ⧸ Subgroup.center L)) ∧
    ∃ r ∈ Subgroup.normalizer ((P : Subgroup L) : Set L),
      (∀ z ∈ (P : Subgroup L) ⊓ Subgroup.centralizer ((P : Subgroup L) : Set L),
        r * z = z * r) ∧
      ∀ X : Subgroup L, X ≤ P → (P : Subgroup L) ≤ Subgroup.normalizer (X : Set L) →
        r ∈ Subgroup.normalizer (X : Set L) →
        X ≤ (P : Subgroup L) ⊓ Subgroup.centralizer ((P : Subgroup L) : Set L) ∨
          X = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Z := Subgroup.center L with hZdef
  set π := QuotientGroup.mk' Z with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have : IsSimpleGroup (L ⧸ Z) := hLq.2
  have hnab : ∃ a b : L ⧸ Z, a * b ≠ b * a :=
    Helpers.quasisimple_central_quotient_nonabelian L hLq
  have hZb : Subgroup.center (L ⧸ Z) = ⊥ := Helpers.center_eq_bot (L ⧸ Z) hnab
  have hI : IsGoldTypeI L := Or.inr (Or.inr ⟨2, le_rfl, ⟨e⟩⟩)
  have hI' : IsGoldTypeI (L ⧸ Z) := isGoldTypeI_quotient_center hZb hI
  set PT := (P : Subgroup L) with hPT
  have hPZ : ∀ t ∈ PT, t ∈ Z → t = 1 := by
    intro t ht htZ
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨t, ht⟩
    exact hZ2 t htZ k (by simpa using congrArg Subtype.val hk)
  have hinj : ∀ s ∈ PT, ∀ t ∈ PT, π s = π t → s = t := by
    intro s hs t ht hst
    have hz : s⁻¹ * t ∈ Z := by
      rw [← QuotientGroup.eq]
      exact hst
    have := hPZ _ (PT.mul_mem (PT.inv_mem hs) ht) hz
    rw [inv_mul_eq_one] at this
    exact this
  set Pb : Sylow 2 (L ⧸ Z) := P.mapSurjective hπs with hPb
  have hPbcoe : (Pb : Subgroup (L ⧸ Z)) = PT.map π := Sylow.coe_mapSurjective _ _
  set PB := (Pb : Subgroup (L ⧸ Z)) with hPB
  set ZP := PB ⊓ Subgroup.centralizer (PB : Set (L ⧸ Z)) with hZP
  obtain ⟨D, hDN, -, -, -, -, hDC, -, -, -, hnabc, -, -, hU, -, -, -, -, -⟩ :=
    h32 (L ⧸ Z) hI' Pb
  obtain ⟨hZc, hPc, hDc⟩ := hU 2 le_rfl ⟨e⟩
  rw [← hPB, ← hZP] at hZc
  rw [← hPB] at hPc
  norm_num at hZc hPc hDc
  have hcardP : Nat.card PT = 64 := by
    rw [← card_map_eq_of_injOn π hinj, ← hPbcoe]
    exact hPc
  set ZT := PT ⊓ Subgroup.centralizer (PT : Set L) with hZT
  have hmemZT : ∀ t ∈ PT, π t ∈ ZP → t ∈ ZT := by
    intro t ht htZ
    refine ⟨ht, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp htZ.2 (π s) (by rw [hPbcoe]; exact ⟨s, hs, rfl⟩)
    rw [← map_mul, ← map_mul] at h1
    exact hinj _ (PT.mul_mem hs ht) _ (PT.mul_mem ht hs) h1
  have hmapZT : ZT.map π = ZP := by
    apply le_antisymm
    · rintro _ ⟨t, ht, rfl⟩
      refine ⟨by rw [hPbcoe]; exact ⟨t, ht.1, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro x hx
      rw [hPbcoe] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp ht.2 s hs]
    · intro x hx
      have hx1 := hx.1
      rw [hPbcoe] at hx1
      obtain ⟨t, ht, rfl⟩ := hx1
      exact ⟨t, hmemZT t ht hx, rfl⟩
  have hinjZT : ∀ s ∈ ZT, ∀ t ∈ ZT, π s = π t → s = t := fun s hs t ht =>
    hinj s hs.1 t ht.1
  have hcardZT : Nat.card ZT = 4 := by
    rw [← card_map_eq_of_injOn π hinjZT, hmapZT]
    exact hZc
  have hPBnab : ¬ IsMulCommutative PB := by
    intro hab
    have hle : PB ≤ ZP := fun x hx => ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)⟩
    have := Subgroup.card_le_of_le hle
    rw [hPc, hZc] at this
    omega
  obtain ⟨hcommPB, -, -⟩ := hnabc hPBnab
  rw [← hZP] at hcommPB
  have heq_of_map : ∀ X Y : Subgroup L, X ≤ PT → Y ≤ PT → X.map π ≤ Y.map π → X ≤ Y := by
    intro X Y hX hY hXY x hx
    obtain ⟨y, hy, hyx⟩ := hXY ⟨x, hx, rfl⟩
    rwa [← hinj y (hY hy) x (hX hx) hyx]
  have hcommP : ⁅PT, PT⁆ = ZT := by
    have hmap : ⁅PT, PT⁆.map π = ZT.map π := by
      rw [Subgroup.map_commutator, ← hPbcoe, hcommPB, hmapZT]
    have hcP : ⁅PT, PT⁆ ≤ PT := Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_def]
      exact PT.mul_mem (PT.mul_mem (PT.mul_mem hx hy) (PT.inv_mem hx)) (PT.inv_mem hy)
    exact le_antisymm (heq_of_map _ _ hcP inf_le_left hmap.le)
      (heq_of_map _ _ inf_le_left hcP hmap.ge)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 5 (by rw [hDc]; norm_num)
  set rb : L ⧸ Z := (d : L ⧸ Z) with hrb
  have hrb5 : rb ^ 5 = 1 := by
    rw [hrb, ← Subgroup.orderOf_coe, ← pow_orderOf_eq_one (d : L ⧸ Z)] at *
    rw [← hd, Subgroup.orderOf_coe]
  have hrb1 : rb ≠ 1 := by
    intro h1
    rw [← Subgroup.orderOf_coe, ← hrb, h1, orderOf_one] at hd
    omega
  have hrbN : rb ∈ Subgroup.normalizer (PB : Set (L ⧸ Z)) := hDN d.2
  have hrbC : rb ∉ Subgroup.centralizer (PB : Set (L ⧸ Z)) := by
    intro h1
    have h2 : rb ∈ D ⊓ Subgroup.centralizer (PB : Set (L ⧸ Z)) := ⟨d.2, h1⟩
    rw [hDC, Subgroup.mem_bot] at h2
    exact hrb1 h2
  have hrbNZ : rb ∈ Subgroup.normalizer (ZP : Set (L ⧸ Z)) :=
    normalizer_le_normalizer_inf_centralizer PB hrbN
  have hZPC : ZP ≤ Subgroup.centralizer ({rb} : Set (L ⧸ Z)) := by
    have hmod := card_modEq_card_inf_centralizer hrb5 hrbNZ
    rw [hZc] at hmod
    set m := Nat.card (ZP ⊓ Subgroup.centralizer ({rb} : Set (L ⧸ Z)) : Subgroup (L ⧸ Z))
      with hm
    have hdvd : m ∣ 4 := hZc ▸ Subgroup.card_dvd_of_le inf_le_left
    have hm4 : m = 4 := eq_four_of_modEq hdvd hmod
    have heq : ZP ⊓ Subgroup.centralizer ({rb} : Set (L ⧸ Z)) = ZP :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZc, ← hm, hm4])
    exact heq ▸ inf_le_right
  have hCPb : PB ⊓ Subgroup.centralizer ({rb} : Set (L ⧸ Z)) = ZP := by
    have hZle : ZP ≤ PB ⊓ Subgroup.centralizer ({rb} : Set (L ⧸ Z)) := le_inf inf_le_left hZPC
    have hmod := card_modEq_card_inf_centralizer hrb5 hrbN
    rw [hPc] at hmod
    have hdvd : Nat.card (PB ⊓ Subgroup.centralizer ({rb} : Set (L ⧸ Z)) : Subgroup _) ∣
        64 := hPc ▸ Subgroup.card_dvd_of_le inf_le_left
    have h4 : 4 ∣ Nat.card (PB ⊓ Subgroup.centralizer ({rb} : Set (L ⧸ Z)) : Subgroup _) :=
      hZc ▸ Subgroup.card_dvd_of_le hZle
    rcases eq_four_or_eq_of_modEq hdvd h4 (by simpa [Nat.ModEq] using hmod.symm) with h | h
    · exact (Subgroup.eq_of_le_of_card_ge hZle (by rw [h, hZc])).symm
    · exfalso
      have hPle : PB ≤ Subgroup.centralizer ({rb} : Set (L ⧸ Z)) := by
        have heq : PB ⊓ Subgroup.centralizer ({rb} : Set (L ⧸ Z)) = PB :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hPc])
        exact heq ▸ inf_le_right
      apply hrbC
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hPle hx))
  obtain ⟨r, hr⟩ := hπs rb
  have hrN : r ∈ Subgroup.normalizer (PT : Set L) := by
    apply G3a.mem_normalizer_of_map P
    rw [← hπdef, hr, ← hPbcoe]
    exact hrbN
  refine ⟨hcardP, hcardZT, hcommP, hmapZT, r, hrN, ?_, ?_⟩
  ·
    intro z hz
    have h1 : r * z * r⁻¹ ∈ PT := (Subgroup.mem_normalizer_iff.mp hrN z).mp hz.1
    have h2 : π (r * z * r⁻¹) = π z := by
      rw [map_mul, map_mul, map_inv, hr]
      have := Subgroup.mem_centralizer_singleton_iff.mp
        (hZPC (hmapZT ▸ ⟨z, hz, rfl⟩ : π z ∈ ZP))
      rw [← this]
      group
    have h3 := hinj _ h1 z hz.1 h2
    calc r * z = r * z * r⁻¹ * r := by group
      _ = z * r := by rw [h3]
  ·
    intro X hXP hPX hrX
    set XB := X.map π with hXB
    have hXBP : XB ≤ PB := by rw [hPbcoe]; exact Subgroup.map_mono hXP
    have hPXB : PB ≤ Subgroup.normalizer (XB : Set (L ⧸ Z)) := by
      rw [hPbcoe]
      exact (Subgroup.map_mono hPX).trans (Subgroup.le_normalizer_map π)
    have hrXB : rb ∈ Subgroup.normalizer (XB : Set (L ⧸ Z)) := by
      rw [← hr]
      exact Subgroup.le_normalizer_map π ⟨r, hrX, rfl⟩
    set YB := XB ⊔ ZP with hYB
    have hYBP : YB ≤ PB := sup_le hXBP inf_le_left
    have hrYB : rb ∈ Subgroup.normalizer (YB : Set (L ⧸ Z)) := by
      rw [← CFSG.Walter.map_conj_eq_iff_mem_normalizer, hYB, Subgroup.map_sup,
        CFSG.Walter.map_conj_eq_iff_mem_normalizer.mpr hrXB,
        CFSG.Walter.map_conj_eq_iff_mem_normalizer.mpr hrbNZ]
    have hYC : YB ⊓ Subgroup.centralizer ({rb} : Set (L ⧸ Z)) = ZP := by
      apply le_antisymm
      · rw [← hCPb]
        exact inf_le_inf_right _ hYBP
      · exact le_inf le_sup_right hZPC
    have hmod := card_modEq_card_inf_centralizer hrb5 hrYB
    rw [hYC, hZc] at hmod
    have hdvd : Nat.card YB ∣ 64 := hPc ▸ Subgroup.card_dvd_of_le hYBP
    have h4 : 4 ∣ Nat.card YB := hZc ▸ Subgroup.card_dvd_of_le (le_sup_right : ZP ≤ YB)
    rcases eq_four_or_eq_of_modEq hdvd h4 hmod with h | h
    ·
      left
      have hYZ : YB = ZP := (Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h, hZc])).symm
      intro x hx
      exact hmemZT x (hXP hx) (hYZ ▸ (le_sup_left : XB ≤ YB) ⟨x, hx, rfl⟩)
    ·
      right
      have hYP : YB = PB := Subgroup.eq_of_le_of_card_ge hYBP (by rw [h, hPc])
      have hZXB : ZP ≤ XB := by
        rw [← hcommPB, Subgroup.commutator_le]
        intro p hp q hq
        have hset : ((XB ⊔ ZP : Subgroup (L ⧸ Z)) : Set (L ⧸ Z)) =
            (XB : Set (L ⧸ Z)) * (ZP : Set (L ⧸ Z)) :=
          Subgroup.coe_mul_of_right_le_normalizer_left XB ZP (inf_le_left.trans hPXB)
        have hp' : p ∈ ((XB ⊔ ZP : Subgroup (L ⧸ Z)) : Set (L ⧸ Z)) := by
          rw [← hYB, hYP]
          exact hp
        have hq' : q ∈ ((XB ⊔ ZP : Subgroup (L ⧸ Z)) : Set (L ⧸ Z)) := by
          rw [← hYB, hYP]
          exact hq
        rw [hset] at hp' hq'
        obtain ⟨x, hx, z, hz, rfl⟩ := Set.mem_mul.mp hp'
        obtain ⟨x', hx', z', hz', rfl⟩ := Set.mem_mul.mp hq'
        have hzc : ∀ y ∈ PB, y * z = z * y := fun y hy =>
          Subgroup.mem_centralizer_iff.mp hz.2 y hy
        have hzc' : ∀ y ∈ PB, y * z' = z' * y := fun y hy =>
          Subgroup.mem_centralizer_iff.mp hz'.2 y hy
        have e1 : ⁅x * z, x' * z'⁆ = ⁅x, x'⁆ := by
          rw [commutatorElement_def, commutatorElement_def]
          have ha := hzc x' (hXBP hx')
          have hb := hzc' x (hXBP hx)
          have hc := hzc z' hz'.1
          calc x * z * (x' * z') * (x * z)⁻¹ * (x' * z')⁻¹
              = x * (z * x') * z' * z⁻¹ * x⁻¹ * z'⁻¹ * x'⁻¹ := by group
            _ = x * (x' * z) * z' * z⁻¹ * x⁻¹ * z'⁻¹ * x'⁻¹ := by rw [ha]
            _ = x * x' * (z * z') * z⁻¹ * x⁻¹ * z'⁻¹ * x'⁻¹ := by group
            _ = x * x' * (z' * z) * z⁻¹ * x⁻¹ * z'⁻¹ * x'⁻¹ := by rw [hc]
            _ = x * x' * (z' * x⁻¹) * z'⁻¹ * x'⁻¹ := by group
            _ = x * x' * (x⁻¹ * z') * z'⁻¹ * x'⁻¹ := by
                rw [(hzc' x⁻¹ (PB.inv_mem (hXBP hx)))]
            _ = x * x' * x⁻¹ * x'⁻¹ := by group
        rw [e1, commutatorElement_def]
        exact XB.mul_mem (XB.mul_mem (XB.mul_mem hx hx') (XB.inv_mem hx)) (XB.inv_mem hx')
      have hXBeq : XB = PB := by
        rw [← hYP, hYB, sup_eq_left.mpr hZXB]
      apply le_antisymm hXP
      rw [hPbcoe] at hXBeq
      exact heq_of_map _ _ le_rfl hXP hXBeq.ge

end Sylow

end G76

end CFSG.Goldschmidt
