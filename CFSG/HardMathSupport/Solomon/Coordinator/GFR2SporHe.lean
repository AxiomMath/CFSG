module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporHat
public import Certificates.Certificate36901
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Model
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporRed
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.Sporadic.HeldB.CertPBridge
public import Certificates.Certificate13515

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Solomon.Coordinator.B3S3
  CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Mathieu CFSG.RankThree.Native

theorem normal_of_isSubnormal_prime_relIndex {G : Type*} [Group G] :
    ∀ {H K : Subgroup G}, CFSG.Open.IsSubnormal H K → (H.relIndex K).Prime →
      (H.subgroupOf K).Normal := by
  intro H K h
  induction h with
  | refl H =>
    intro hp
    rw [Subgroup.relIndex_self] at hp
    exact absurd hp Nat.not_prime_one
  | @step H M K hHM hN hMK ih =>
    intro hp
    have hmul : H.relIndex M * M.relIndex K = H.relIndex K :=
      Subgroup.relIndex_mul_relIndex H M K hHM hMK.le
    rw [← hmul] at hp
    rcases Nat.prime_mul_iff.1 hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    · have hKM : K ≤ M := Subgroup.relIndex_eq_one.1 hp2
      have : M = K := le_antisymm hMK.le hKM
      subst this
      exact hN
    · have hMH : M ≤ H := Subgroup.relIndex_eq_one.1 hp2
      have : H = M := le_antisymm hHM hMH
      subst this
      exact ih hp1

theorem no_subnormal_1080_of_words {G : Type*} [Group G] {C I : Subgroup G} {a b c : G}
    (hC : Nat.card C = 7560) (hgen : Subgroup.closure ({a, b, c} : Set G) = C)
    (ha : a ^ 3 = 1) (hb : (b * c * c) ^ 12 = 1) (hc : (b * b * c) ^ 12 = 1)
    (hI : CFSG.Open.IsSubnormal I C) (hcard : Nat.card I = 1080) : False := by
  have hIC : I ≤ C := hI.le
  have h1 : Nat.card ↥(I.subgroupOf C) = 1080 := by
    rw [← hcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIC).toEquiv
  have h2 : (I.subgroupOf C).index = 7 := by
    have := Subgroup.card_mul_index (I.subgroupOf C)
    rw [h1, hC] at this
    omega
  have hprime : (I.relIndex C).Prime := by
    rw [Subgroup.relIndex, h2]; norm_num
  have hN := normal_of_isSubnormal_prime_relIndex hI hprime
  have hQ : Nat.card (↥C ⧸ I.subgroupOf C) = 7 := by
    rw [← Subgroup.index, h2]
  have hpow : ∀ x : ↥C ⧸ I.subgroupOf C, x ^ 7 = 1 := fun x => by
    have := pow_card_eq_one' (G := ↥C ⧸ I.subgroupOf C) (x := x)
    rwa [hQ] at this
  have hmemC : ∀ y ∈ ({a, b, c} : Set G), y ∈ C := fun y hy => hgen ▸ Subgroup.subset_closure hy
  have ha' : a ∈ C := hmemC a (by simp)
  have hb' : b ∈ C := hmemC b (by simp)
  have hc' : c ∈ C := hmemC c (by simp)
  let ψ : ↥C →* ↥C ⧸ I.subgroupOf C := QuotientGroup.mk' (I.subgroupOf C)
  have one_of_coprime : ∀ (x : ↥C ⧸ I.subgroupOf C) (m : ℕ), x ^ m = 1 → Nat.Coprime m 7 →
      x = 1 := by
    intro x m hm hcop
    have := pow_gcd_eq_one.2 ⟨hm, hpow x⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have ψa : ψ ⟨a, ha'⟩ = 1 := by
    refine one_of_coprime _ 3 ?_ (by norm_num)
    rw [← map_pow]
    have : (⟨a, ha'⟩ : ↥C) ^ 3 = 1 := Subtype.ext ha
    rw [this, map_one]
  have ψbcc : ψ ⟨b, hb'⟩ * ψ ⟨c, hc'⟩ * ψ ⟨c, hc'⟩ = 1 := by
    refine one_of_coprime _ 12 ?_ (by norm_num)
    rw [← map_mul, ← map_mul, ← map_pow]
    have : ((⟨b, hb'⟩ : ↥C) * ⟨c, hc'⟩ * ⟨c, hc'⟩) ^ 12 = 1 := Subtype.ext hb
    rw [this, map_one]
  have ψbbc : ψ ⟨b, hb'⟩ * ψ ⟨b, hb'⟩ * ψ ⟨c, hc'⟩ = 1 := by
    refine one_of_coprime _ 12 ?_ (by norm_num)
    rw [← map_mul, ← map_mul, ← map_pow]
    have : ((⟨b, hb'⟩ : ↥C) * ⟨b, hb'⟩ * ⟨c, hc'⟩) ^ 12 = 1 := Subtype.ext hc
    rw [this, map_one]
  generalize hu_def : ψ ⟨b, hb'⟩ = u at ψbcc ψbbc
  generalize hv_def : ψ ⟨c, hc'⟩ = v at ψbcc ψbbc
  have hu : u = v⁻¹ * v⁻¹ := by
    calc u = (u * v * v) * v⁻¹ * v⁻¹ := by group
      _ = v⁻¹ * v⁻¹ := by rw [ψbcc]; group
  have hv3 : v ^ 3 = 1 := by
    rw [hu] at ψbbc
    calc v ^ 3 = (v⁻¹ * v⁻¹ * (v⁻¹ * v⁻¹) * v)⁻¹ := by group
      _ = 1 := by rw [ψbbc]; simp
  have hv1 : v = 1 := one_of_coprime v 3 hv3 (by norm_num)
  have hu1 : u = 1 := by rw [hu, hv1]; simp
  rw [hv1] at hv_def
  rw [hu1] at hu_def
  have memI : ∀ (y : G) (hy : y ∈ C), ψ ⟨y, hy⟩ = 1 → y ∈ I := fun y hy h =>
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h)
  have hCI : C ≤ I := by
    rw [← hgen, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact memI _ ha' ψa
    · exact memI _ hb' hu_def
    · exact memI _ hc' hv_def
  have : Nat.card I = Nat.card C := by rw [le_antisymm hIC hCI]
  omega

theorem heC0Words_sound {g : Array (Array ℕ)} (h : heC0Words g = true) :
    g.size = 3 ∧ permOfArr 8330 g[0]! ^ 3 = 1 ∧
      (permOfArr 8330 g[1]! * permOfArr 8330 g[2]! * permOfArr 8330 g[2]!) ^ 12 = 1 ∧
      (permOfArr 8330 g[1]! * permOfArr 8330 g[1]! * permOfArr 8330 g[2]!) ^ 12 = 1 := by
  unfold heC0Words at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hsz, h0⟩, h1⟩, h2⟩, hc0⟩, hc1⟩, hc2⟩ := h
  have r0 := rep_of_validA h0
  have r1 := rep_of_validA h1
  have r2 := rep_of_validA h2
  refine ⟨hsz, (eqA_iff (rep_powArr r0 3) rep_idA).1 hc0, ?_, ?_⟩
  · exact (eqA_iff (rep_powArr (rep_compA (rep_compA r1 r2) r2) 12) rep_idA).1 hc1
  · exact (eqA_iff (rep_powArr (rep_compA (rep_compA r1 r1) r2) 12) rep_idA).1 hc2

theorem permsA_three {n : ℕ} {gs : Array (Array ℕ)} (h : gs.size = 3) :
    permsA n gs = {permOfArr n gs[0]!, permOfArr n gs[1]!, permOfArr n gs[2]!} := by
  ext x
  simp only [permsA, h, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩

theorem map_conj_inv_centralizer_inf {G : Type*} [Group G] {P : Subgroup G} {k y : G} (hk : k ∈ P) :
    (Subgroup.centralizer ({k * y * k⁻¹} : Set G) ⊓ P).map (MulAut.conj k⁻¹).toMonoidHom =
      Subgroup.centralizer ({y} : Set G) ⊓ P := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨w, ⟨hwc, hwP⟩, rfl⟩
    refine ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hwP) hk⟩
    calc k⁻¹ * w * k * y = k⁻¹ * (w * (k * y * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * y * k⁻¹) * w) * k := by rw [hwc]
      _ = y * (k⁻¹ * w * k) := by group
  · rintro ⟨hzc, hzP⟩
    refine ⟨k * z * k⁻¹, ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩, by group⟩
    calc k * z * k⁻¹ * (k * y * k⁻¹) = k * (z * y) * k⁻¹ := by group
      _ = k * (y * z) * k⁻¹ := by rw [hzc]
      _ = k * y * k⁻¹ * (k * z * k⁻¹) := by group

theorem centralizer_pow_eq_of_pow_three {G : Type*} [Group G] {X : G} (hX : X ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) :
    Subgroup.centralizer ({X ^ e} : Set G) = Subgroup.centralizer ({X} : Set G) := by
  rcases he with rfl | rfl
  · rw [pow_one]
  · apply le_antisymm
    · intro z hz
      have hz' : z * X ^ 2 = X ^ 2 * z := Subgroup.mem_centralizer_singleton_iff.1 hz
      have hy4 : X = (X ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hX, one_mul, pow_one]
      rw [Subgroup.mem_centralizer_singleton_iff, hy4]
      exact Commute.pow_right hz' 2
    · intro z hz
      have hz' : z * X = X * z := Subgroup.mem_centralizer_singleton_iff.1 hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Commute.pow_right (show Commute z X from hz') 2).eq

theorem he_pumpup_model
    {t : Equiv.Perm (Fin 8330)} (ht : t ∈ heP)
    (ht3 : orderOf t = 3) {I : Subgroup (Equiv.Perm (Fin 8330))}
    (hI : CFSG.Open.IsSubnormal I
      (Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 8330))) ⊓ heP))
    (h1080 : 1080 ≤ Nat.card I) :
    GLAPPrimeCoreOf 3 I = ⊥ ∧ Nat.card I ≤ 7560 ∧ Nat.card I ≠ 1080 := by
  have hP := Certificates.certificate13515
  obtain ⟨c, hc, k, hk, e, he, htk⟩ := hP.1 t ht ht3
  have hX3 : permOfArr 8330 heS3CaseX[c]! ^ 3 = 1 :=
    (hP.2.1 c hc).2.1 ▸ pow_orderOf_eq_one (permOfArr 8330 heS3CaseX[c]!)
  have hcrit := (hP.2.1 c hc).2.2
  have hinj : Function.Injective (MulAut.conj k⁻¹).toMonoidHom := (MulAut.conj k⁻¹).injective
  have hcardI : Nat.card (I.map (MulAut.conj k⁻¹).toMonoidHom) = Nat.card I :=
    Subgroup.card_map_of_injective hinj
  have hcore : (GLAPPrimeCoreOf 3 I).map (MulAut.conj k⁻¹).toMonoidHom =
      GLAPPrimeCoreOf 3 (I.map (MulAut.conj k⁻¹).toMonoidHom) :=
    map_glaPPrimeCoreOf_of_injective 3 _ hinj I
  have hI'' := hI.map (MulAut.conj k⁻¹).toMonoidHom
  rw [htk, map_conj_inv_centralizer_inf hk, centralizer_pow_eq_of_pow_three hX3 he] at hI''
  generalize I.map (MulAut.conj k⁻¹).toMonoidHom = I'' at hcardI hcore hI''
  have hle := Subgroup.card_le_of_le hI''.le
  have hc2 : c = 0 ∨ c = 1 := by omega
  rcases hc2 with rfl | rfl
  · have hcard := hP.2.2.1
    rw [hcard] at hle
    have hcl := hP.2.2.2.2.1
    obtain ⟨hsz, hg1, hg2, hg3⟩ :=
      heC0Words_sound (g := heS3C0Gens) Certificates.certificate36901
    rw [permsA_three hsz] at hcl
    refine ⟨?_, ?_, ?_⟩
    · have h1 := GLAPPrimeCoreOf_le_of_isSubnormal_sub Nat.prime_three hI''
      rw [hcrit, le_bot_iff, ← hcore] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h1
    · omega
    · intro h1080'
      exact no_subnormal_1080_of_words hcard hcl hg1 hg2 hg3 hI'' (hcardI.trans h1080')
  · rw [hP.2.2.2.1] at hle
    omega

theorem sporNoPumpup_He
    (hSpM : SporadicMultipliers) (hOG : UniquenessMaximal.InputONGroup)
    (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) : SporNoPumpup .He := by
  intro Y _ _ hq _hKg hcore ⟨e⟩ x hxo J₁ hJ₁ hty
  have hcen : Subgroup.center Y = ⊥ :=
    center_eq_bot_of_not_three_dvd hSpM (by decide) hq hcore e
  obtain ⟨s, hs3, hs⟩ := hatCfg_of_component hOut hq e hxo
  obtain ⟨-, hsub⟩ := hs J₁ hJ₁.2.1
  have h1080 := gfr2spor_card_ge hOG hty
  let φ : (TauCeti.CFSGIndex.sporadic .He).Group ≃* ↥heP :=
    ((hbr .He).some).symm.trans heEquivP
  let ρ : Y →* Equiv.Perm (Fin 8330) := (heP.subtype.comp φ.toMonoidHom).comp (projOf e)
  have hproj : Function.Injective (projOf e) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_projOf e, hcen])
  have hρ : Function.Injective ρ :=
    (heP.subtype_injective.comp φ.injective).comp hproj
  have hmapC : (Subgroup.centralizer ({s} : Set _)).map (heP.subtype.comp φ.toMonoidHom) =
      Subgroup.centralizer ({(φ s : Equiv.Perm (Fin 8330))} : Set _) ⊓ heP := by
    rw [← Subgroup.map_map, map_centralizer_mulEquiv, map_centralizer_subtype]
  have hsub' : CFSG.Open.IsSubnormal (J₁.map ρ)
      (Subgroup.centralizer ({(φ s : Equiv.Perm (Fin 8330))} : Set _) ⊓ heP) := by
    have := hsub.map (heP.subtype.comp φ.toMonoidHom)
    rw [hmapC, Subgroup.map_map] at this
    exact this
  have hts : orderOf (φ s : Equiv.Perm (Fin 8330)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hs3
  have hcardJ : Nat.card (J₁.map ρ) = Nat.card J₁ := Subgroup.card_map_of_injective hρ
  obtain ⟨hcoreI, hle, hne⟩ := he_pumpup_model (φ s).2 hts hsub' (by rw [hcardJ]; exact h1080)
  have hbotJ : GLAPPrimeCore 3 ↥J₁ = ⊥ := by
    have h1 := map_glaPPrimeCoreOf_of_injective 3 ρ hρ J₁
    rw [hcoreI] at h1
    have h2 : GLAPPrimeCoreOf 3 J₁ = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ hρ).1 h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ J₁.subtype_injective).1 h2
  have hbarcard : Nat.card (barOf 3 J₁) = Nat.card J₁ := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥J₁)
    have hN1 : Nat.card (GLAPPrimeCore 3 ↥J₁) = 1 := by rw [hbotJ]; exact Subgroup.card_bot
    rw [hN1, mul_one] at h
    exact h.symm
  rcases hty with hON | hSix
  · have hbc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (barOf 3 J₁))
    rw [(UniquenessMaximal.isSimple_card_of_isHatON hOG hON).2, hON.2.1] at hbc
    unfold orderON at hbc
    omega
  · have := gfr2_card_isHatSix hSix
    exact hne (by omega)

end CFSG.HardMathSupport.Solomon.Coordinator
