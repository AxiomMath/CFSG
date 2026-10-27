module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Trans
import CFSG.RankThree.PartOne.K1214.CycAlg
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.RankThree.PartOne
open scoped commutatorElement

theorem stepCaseB_holds :
    Pat4Inv → U42E27 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (B : Subgroup Ω) (x : Ω)
      (L : Subgroup Ω) [L.Normal] (e : ↥L ⧸ Subgroup.center ↥L ≃* S6), Setup B x L →
      ∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → catalogIs ↥K S9.isU4two →
      IsSimpleGroup ↥K → Nat.card ↥K = 25920 →
      (∀ d ∈ D, d ∉ Subgroup.zpowers x → ∀ g : PGU6, Psi g = theta L e d → Pat4 g) →
      Nat.card B ≤ 243 → (∀ b ∈ B, ∃ d ∈ D, ∃ k ∈ K, b = d * k) →
      ∀ b₀ ∈ B, (∀ s : S6, theta L e b₀ ≠ MulAut.conj s) →
      Nat.card B = 243 ∧
        ∃ U : Subgroup PGU6, IsPGroup 2 U ∧ U ≠ ⊥ ∧ Bt B L e ≤ Subgroup.normalizer (U : Set PGU6) := by
  intro hPat4Inv hU42E27 Ω _ _ B x L _ e hsetup D K hpre hcat hKsimple hKcard hPat hBle hBK
    b₀ hb₀B hb₀noninner
  classical
  obtain ⟨hcfg, hMaxG, -⟩ := hsetup
  have hDleB : D ≤ B := hpre.1
  have hD_el : IsElemAbelian 3 D := hpre.2.1
  have hD9 : Nat.card D = 9 := by rw [hpre.2.2.1]; norm_num
  have hxD : x ∈ D := hpre.2.2.2.1
  have hKcomp : IsComponentOf K (L ⊓ Subgroup.centralizer (D : Set Ω)) := hpre.2.2.2.2.2.1
  have hKL : K ≤ L := hKcomp.1.trans inf_le_left
  have hKcentD : K ≤ Subgroup.centralizer (D : Set Ω) := hKcomp.1.trans inf_le_right
  have hDeq : D = B ⊓ Subgroup.centralizer (K : Set Ω) := hpre.2.2.2.2.2.2
  have hDcentK : D ≤ Subgroup.centralizer (K : Set Ω) := hDeq ▸ inf_le_right
  have hB_el : IsElemAbelian 3 B := hcfg.elem
  haveI hLperf : Group.IsPerfect ↥L := isPerfect_of_cfg hcfg
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxcent : x ∈ Subgroup.centralizer (L : Set Ω) :=
    (hcfg.cent x hcfg.mem).2 (Subgroup.mem_zpowers x)
  have hxle : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set Ω) :=
    Subgroup.zpowers_le.mpr hxcent
  have hxθ : theta L e x = 1 := (theta_eq_one_iff e x).2 hxcent
  have hx3 : x ^ 3 = 1 := hB_el.2 x hcfg.mem
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hcfg.ne_one
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hxord]
  obtain ⟨d, hdD, k, hkK, hbk⟩ := hBK b₀ hb₀B
  have hkL : k ∈ L := hKL hkK
  have hkθ : theta L e k = MulAut.conj (piL e ⟨k, hkL⟩) := theta_coe e ⟨k, hkL⟩
  have hdnoninner : ∀ s : S6, theta L e d ≠ MulAut.conj s := by
    intro s hs
    refine hb₀noninner (s * piL e ⟨k, hkL⟩) ?_
    calc theta L e b₀ = theta L e (d * k) := by rw [hbk]
      _ = theta L e d * theta L e k := map_mul _ _ _
      _ = MulAut.conj s * MulAut.conj (piL e ⟨k, hkL⟩) := by rw [hs, hkθ]
      _ = MulAut.conj (s * piL e ⟨k, hkL⟩) := (map_mul MulAut.conj s (piL e ⟨k, hkL⟩)).symm
  have hdnotin : d ∉ Subgroup.zpowers x := by
    intro hdmem
    refine hdnoninner 1 ?_
    rw [(theta_eq_one_iff e d).2 (hxle hdmem)]
    simp
  have hd3 : d ^ 3 = 1 := hD_el.2 d hdD
  have hθd3 : theta L e d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  obtain ⟨g, hg⟩ := exists_Psi_of_pow_three (theta L e d) hθd3
  have hpat : Pat4 g := hPat d hdD hdnotin g hg
  have hgnotin : g ∉ iota.range := by
    rintro ⟨s, hs⟩
    refine hdnoninner s ?_
    rw [← hg, ← hs, Psi_iota]
  obtain ⟨t, ht2, ht1, htfix, htcomm⟩ := hPat4Inv g hpat hgnotin
  have hd_fix : theta L e d t = t := by rw [← hg]; exact htfix
  have hKnab : ¬ IsMulCommutative ↥K := by
    intro hc
    haveI : IsMulCommutative ↥K := hc
    have hp : Nat.Prime (Nat.card ↥K) := (Group.is_simple_iff_prime_card).1 hKsimple
    rw [hKcard] at hp
    exact (by norm_num : ¬ Nat.Prime 25920) hp
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    rcases hKsimple.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆) with
      h | h
    · exact absurd ((commutator_eq_bot_iff ↥K).1 h) hKnab
    · exact h
  have hKperf : ⁅K, K⁆ = K := by
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥K)) (H₂ := (⊤ : Subgroup ↥K))
      K.subtype
    simp only [hKtop, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.symm
  have himLperf : ⁅imL e K, imL e K⁆ = imL e K := imL_perfect e hKL hKperf
  have himLfix : imL e K ≤ fixSubgroup (Psi g) := by
    rw [show Psi g = theta L e d from hg]
    exact imL_le_fixSubgroup e (fun h hh => (Subgroup.mem_centralizer_iff.1 (hKcentD hh)) d hdD)
  have hcommt : ∀ s ∈ imL e K, s * t = t * s := htcomm (imL e K) himLfix himLperf
  have hkfix : ∀ k' ∈ K, theta L e k' t = t := by
    intro k' hk'
    have hkL' : k' ∈ L := hKL hk'
    have hpiL : piL e ⟨k', hkL'⟩ ∈ imL e K := by
      rw [imL]
      exact Subgroup.mem_map.mpr ⟨⟨k', hkL'⟩, hk', rfl⟩
    rw [theta_coe e ⟨k', hkL'⟩, MulAut.conj_apply]
    calc piL e ⟨k', hkL'⟩ * t * (piL e ⟨k', hkL'⟩)⁻¹
        = (t * piL e ⟨k', hkL'⟩) * (piL e ⟨k', hkL'⟩)⁻¹ := by rw [hcommt _ hpiL]
      _ = t := by group
  let ψ : ↥D →* MulAut S6 := (theta L e).comp D.subtype
  have hψker : ψ.ker = (Subgroup.zpowers x).subgroupOf D := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      change theta L e (y : Ω) = 1 at hy
      exact (hcfg.cent (y : Ω) (hDleB y.2)).mp ((theta_eq_one_iff e (y : Ω)).mp hy)
    · intro hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      show theta L e (y : Ω) = 1
      rw [← hn, map_zpow, hxθ, one_zpow]
  have hxDpow : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hxD
  have hψkercard : Nat.card ↥ψ.ker = 3 := by
    rw [hψker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxDpow).toEquiv, hxcard]
  have hψrangecard : Nat.card ↥ψ.range = 3 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hψkercard, hD9] at h
    omega
  have hψrange : ψ.range = Subgroup.zpowers (theta L e d) := by
    have hle : Subgroup.zpowers (theta L e d) ≤ ψ.range :=
      Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨⟨d, hdD⟩, rfl⟩)
    have hcard : Nat.card ↥(Subgroup.zpowers (theta L e d)) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [← map_pow (theta L e) d 3, hd3, map_one])
        (fun h => hdnoninner 1 (by rw [h]; exact (map_one (MulAut.conj)).symm))]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hψrangecard, hcard])).symm
  let S : Subgroup Ω := (MulAction.stabilizer (MulAut S6) t).comap (theta L e)
  have hmemS : ∀ f : Ω, f ∈ S ↔ theta L e f t = t := by
    intro f
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  have hDleS : D ≤ S := by
    intro y hy
    have hyD : ψ ⟨y, hy⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩
    have hle : ψ.range ≤ MulAction.stabilizer (MulAut S6) t := by
      rw [hψrange]
      exact Subgroup.zpowers_le.mpr
        (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hd_fix)
    have h2 := hle hyD
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2
  have hDfix : ∀ y ∈ D, theta L e y t = t := fun y hy => (hmemS y).1 (hDleS hy)
  obtain ⟨A₀, hA₀el, hA₀card⟩ := hU42E27 ↥K hcat
  let A : Subgroup Ω := A₀.map K.subtype
  have hAK : A ≤ K := by
    rintro a ⟨a₀, -, rfl⟩
    exact a₀.2
  have hAel : IsElemAbelian 3 A := hA₀el.map K.subtype
  have hAcard : Nat.card A = 27 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hA₀card]
  have hDAcomm : ∀ a ∈ D, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.1 (hDcentK ha)) b (hAK hb)).symm
  have hAleS : A ≤ S := by
    intro a ha
    have haK : a ∈ K := hAK ha
    have haL : a ∈ L := hKL haK
    rw [hmemS]
    have hpiL : piL e ⟨a, haL⟩ ∈ imL e K := by
      rw [imL]
      exact Subgroup.mem_map.mpr ⟨⟨a, haL⟩, haK, rfl⟩
    rw [theta_coe e ⟨a, haL⟩, MulAut.conj_apply]
    calc piL e ⟨a, haL⟩ * t * (piL e ⟨a, haL⟩)⁻¹
        = (t * piL e ⟨a, haL⟩) * (piL e ⟨a, haL⟩)⁻¹ := by rw [hcommt _ hpiL]
      _ = t := by group
  let F : Subgroup Ω := D ⊔ A
  have hFel : IsElemAbelian 3 F := IsElemAbelian.sup_of_commute hD_el hAel hDAcomm
  have hFS : F ≤ S := sup_le hDleS hAleS
  have hFfix : ∀ f ∈ F, theta L e f t = t := fun f hf => (hmemS f).1 (hFS hf)
  have hDAbot : D ⊓ A = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    have hyK : y ∈ K := hAK hy.2
    have hyC : y ∈ Subgroup.centralizer (K : Set Ω) := hDcentK hy.1
    have hcenter : Subgroup.center ↥K = ⊥ := by
      rcases hKsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
      · exact h
      · exact absurd (Subgroup.center_eq_top_iff.1 h) hKnab
    have hmem : (⟨y, hyK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k'
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hyC k' k'.2)
    rw [hcenter, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hFcard : Nat.card F = 243 := by
    obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (H := Ω) D A hDAcomm
    rw [hDAbot, Subgroup.card_bot, mul_one, hD9, hAcard] at h1
    rw [h1]
  let P : Subgroup ↥L := (Subgroup.zpowers t).comap (piL e)
  let φ : ↥P →* ↥(Subgroup.zpowers t) :=
    { toFun := fun y => ⟨piL e (y : ↥L), Subgroup.mem_comap.mp y.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨l, hl⟩ := piL_surjective e (y : S6)
    have hlP : l ∈ P := by
      rw [Subgroup.mem_comap]
      exact hl ▸ y.2
    exact ⟨⟨l, hlP⟩, Subtype.ext hl⟩
  have htcard : Nat.card ↥(Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1]
  have hφker : φ.ker ≤ Subgroup.center ↥P := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro z
    have hy1 : piL e (y : ↥L) = 1 := by
      have h : (⟨piL e (y : ↥L), Subgroup.mem_comap.mp y.2⟩ : ↥(Subgroup.zpowers t)) = 1 :=
        MonoidHom.mem_ker.mp hy
      exact congrArg Subtype.val h
    have hyZ : (y : ↥L) ∈ Subgroup.center ↥L := by
      rw [← ker_piL e, MonoidHom.mem_ker]
      exact hy1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hyZ (z : ↥L)
  have hPcomm : ∀ a b : ↥P, a * b = b * a := by
    haveI hcommP : IsMulCommutative ↥P :=
      MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center φ hφker
    exact fun a b => mul_comm' a b
  have hPcomm' : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hPcomm ⟨a, ha⟩ ⟨b, hb⟩)
  have hP2dvd : 2 ∣ Nat.card ↥P := by
    have h := Subgroup.card_ker_mul_card_range φ
    have htop : Nat.card ↥(⊤ : Subgroup ↥(Subgroup.zpowers t)) = 2 := by
      rw [Nat.card_congr Subgroup.topEquiv.toEquiv, htcard]
    rw [MonoidHom.range_eq_top.mpr hφsurj, htop] at h
    exact ⟨Nat.card ↥φ.ker, h.symm.trans (Nat.mul_comm _ _)⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 hP2dvd
  have hu2 : (u : ↥L) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (u : ↥L)
    rwa [Subgroup.orderOf_coe, hu] at h
  have huP₂ : (u : ↥L) ∈ K1214.torsionSub P hPcomm' 2 := by
    rw [K1214.mem_torsionSub]
    exact ⟨u.2, hu2⟩
  have hune : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hP₂ne : K1214.torsionSub P hPcomm' 2 ≠ ⊥ := by
    intro hbot
    have h1 : (u : ↥L) = 1 := by
      have hmem : (u : ↥L) ∈ (⊥ : Subgroup ↥L) := hbot ▸ huP₂
      simpa using hmem
    exact hune (Subtype.ext h1)
  have hP₂2 : IsPGroup 2 ↥(K1214.torsionSub P hPcomm' 2) := by
    intro y
    obtain ⟨-, hy2⟩ := K1214.mem_torsionSub.mp y.2
    exact ⟨1, Subtype.ext (by simpa using hy2)⟩
  have hU2 : IsPGroup 2 (Subgroup.zpowers (iota t)) := by
    have hcard : Nat.card (Subgroup.zpowers (iota t)) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [← map_pow iota t 2, ht2, map_one])
        (fun h => ht1 (iota_injective (by rw [h, map_one])))]
    exact IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have hUne : Subgroup.zpowers (iota t) ≠ ⊥ := by
    intro hbot
    rw [Subgroup.zpowers_eq_bot] at hbot
    exact ht1 (iota_injective (by rw [hbot, map_one]))
  let W : Subgroup Ω := (K1214.torsionSub P hPcomm' 2).map L.subtype
  let fmap : ↥(K1214.torsionSub P hPcomm' 2) →* ↥W :=
    { toFun := fun z => ⟨L.subtype (z : ↥L), Subgroup.mem_map.mpr ⟨(z : ↥L), z.2, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hfsurj : Function.Surjective fmap := by
    intro y
    obtain ⟨y₀, hy₀, hyeq⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨y₀, hy₀⟩, Subtype.ext hyeq⟩
  have hW2 : IsPGroup 2 ↥W := hP₂2.of_surjective fmap hfsurj
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hbot' : Subgroup.map L.subtype (K1214.torsionSub P hPcomm' 2) = ⊥ := hbot
    exact hP₂ne (Subgroup.map_injective L.subtype_injective (by rw [hbot', Subgroup.map_bot]))
  have hF_le_NW : F ≤ Subgroup.normalizer (W : Set Ω) := by
    rw [Subgroup.le_normalizer_iff]
    intro f hf y hy
    obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
    have hy₀P : piL e y₀ ∈ Subgroup.zpowers t :=
      Subgroup.mem_comap.mp (K1214.mem_torsionSub.mp hy₀).1
    have hLmem : f * (y₀ : Ω) * f⁻¹ ∈ L := (inferInstance : L.Normal).conj_mem (y₀ : Ω) y₀.2 f
    refine Subgroup.mem_map.mpr ⟨⟨f * (y₀ : Ω) * f⁻¹, hLmem⟩, ?_, rfl⟩
    rw [K1214.mem_torsionSub]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_comap, ← theta_piL e f y₀]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy₀P
      rw [← hm, map_zpow, hFfix f hf]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) m
    · obtain ⟨-, hy₀2⟩ := K1214.mem_torsionSub.mp hy₀
      have hy₀2' : (y₀ : Ω) ^ 2 = 1 := by
        rw [← Subgroup.coe_pow L y₀ 2, hy₀2]
        rfl
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      change (f * (y₀ : Ω) * f⁻¹) ^ 2 = 1
      rw [conj_pow, hy₀2']
      group
  have h243 : 243 ≤ Nat.card B := by
    have h := hMaxG F W hFel hW2 hWne hF_le_NW
    rwa [hFcard] at h
  have hBeq : Nat.card B = 243 := le_antisymm hBle h243
  have hBfix : ∀ b ∈ B, theta L e b t = t := by
    intro b hb
    obtain ⟨d', hd'D, k', hk'K, hbk'⟩ := hBK b hb
    rw [hbk', map_mul, MulAut.mul_apply, hkfix k' hk'K, hDfix d' hd'D]
  have hBtN : Bt B L e ≤ Subgroup.normalizer (Subgroup.zpowers (iota t) : Set PGU6) := by
    rw [Subgroup.le_normalizer_iff]
    intro g' hg' y hy
    obtain ⟨b, hbB, hbθ⟩ := (mem_Bt e).mp hg'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hconj : g' * iota t * g'⁻¹ = iota t := by
      rw [← iota_Psi g' t, ← hbθ, hBfix b hbB]
    rw [show g' * (iota t) ^ n * g'⁻¹ = (g' * iota t * g'⁻¹) ^ n from by rw [conj_zpow]]
    rw [hconj]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers (iota t)) n
  exact ⟨hBeq, Subgroup.zpowers (iota t), hU2, hUne, hBtN⟩

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
