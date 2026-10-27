module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25OneGen
public import CFSG.Quasithin.EmptyFaithful.T1515Der3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Cent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Degen
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

section Alt

theorem eq_top_of_commutators_mem {Lg : Type*} [Group Lg] (α : Lg →* alternatingGroup (Fin 5))
    (hα : Function.Surjective α)
    (hshort : ∀ N : Subgroup Lg, N.Normal → N ⊔ α.ker = ⊤ → N = ⊤) {y : Lg} (hy : α y ≠ 1)
    {N : Subgroup Lg} (hN : ∀ l : Lg, l * y * l⁻¹ * y⁻¹ ∈ N) : N = ⊤ := by
  let S₀ : Set Lg := {w | ∃ l : Lg, w = l * y * l⁻¹ * y⁻¹}
  let M : Subgroup Lg := Subgroup.closure S₀
  have hMN : M ≤ N := by
    rw [Subgroup.closure_le]
    rintro w ⟨l, rfl⟩
    exact hN l
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨l, rfl⟩ := hw
      have e : g * (l * y * l⁻¹ * y⁻¹) * g⁻¹ =
          ((g * l) * y * (g * l)⁻¹ * y⁻¹) * (g * y * g⁻¹ * y⁻¹)⁻¹ := by group
      rw [e]
      exact M.mul_mem (Subgroup.subset_closure ⟨g * l, rfl⟩)
        (M.inv_mem (Subgroup.subset_closure ⟨g, rfl⟩))
    | one => simp
    | mul x z _ _ hx hz =>
      have : g * (x * z) * g⁻¹ = (g * x * g⁻¹) * (g * z * g⁻¹) := by group
      rw [this]; exact M.mul_mem hx hz
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]; exact M.inv_mem hx
  have hnc : ∃ g : alternatingGroup (Fin 5), g * α y * g⁻¹ * (α y)⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have : α y ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := hall g
      calc g * α y = (g * α y * g⁻¹ * (α y)⁻¹) * α y * g := by group
        _ = α y * g := by rw [this]; group
    rw [alternatingGroup.center_eq_bot (by simp)] at this
    exact hy ((Subgroup.mem_bot).1 this)
  obtain ⟨g, hg⟩ := hnc
  obtain ⟨l, rfl⟩ := hα g
  have hmem : α (l * y * l⁻¹ * y⁻¹) ∈ M.map α :=
    ⟨l * y * l⁻¹ * y⁻¹, Subgroup.subset_closure ⟨l, rfl⟩, rfl⟩
  have hne : M.map α ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hmem
    apply hg
    simpa [map_mul, map_inv] using hmem
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hmapn : (M.map α).Normal := Subgroup.Normal.map hMn α hα
  have htop : M.map α = ⊤ := (hsimple.eq_bot_or_eq_top_of_normal (M.map α)).resolve_left hne
  have hsup : M ⊔ α.ker = ⊤ := by
    have h := Subgroup.comap_map_eq α M
    rw [htop, Subgroup.comap_top] at h
    exact h.symm
  have hMtop : M = ⊤ := hshort M hMn hsup
  rw [eq_top_iff]
  rw [← hMtop]
  exact hMN

theorem exists_order_three_alt5 : ∃ c : alternatingGroup (Fin 5), orderOf c = 3 := by
  let c : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
  refine ⟨c, ?_⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    show (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ^ 3 = 1
    decide
  · intro h
    have := congrArg Subtype.val h
    revert this
    decide

theorem exists_order_three_lift {L A : Type*} [Group L] [Group A] (α : L →* A)
    (hker : ∀ z, α z = 1 → ∃ k : ℕ, z ^ 2 ^ k = 1) {c : A} (hc : orderOf c = 3) {z : L}
    (hz : α z = c) : ∃ y : L, orderOf y = 3 ∧ α y = c := by
  obtain ⟨k, hk⟩ := hker (z ^ 3) (by rw [map_pow, hz, ← hc]; exact pow_orderOf_eq_one c)
  obtain ⟨r, hr0, hr1⟩ :=
    Nat.chineseRemainder (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) 0 1
  obtain ⟨s, hs⟩ : 2 ^ k ∣ r := (Nat.modEq_zero_iff_dvd).1 hr0
  have hy3 : (z ^ r) ^ 3 = 1 := by
    have hrs : r * 3 = 3 * 2 ^ k * s := by rw [hs]; ring
    rw [← pow_mul, hrs, pow_mul, pow_mul, hk, one_pow]
  have hαy : α (z ^ r) = c := by
    rw [map_pow, hz, ← pow_mod_orderOf, hc]
    have : r % 3 = 1 := by simpa [Nat.ModEq] using hr1
    rw [this, pow_one]
  have hy1 : z ^ r ≠ 1 := by
    intro h
    rw [h, map_one] at hαy
    rw [← hαy, orderOf_one] at hc
    omega
  exact ⟨z ^ r, orderOf_eq_prime hy3 hy1, hαy⟩

end Alt

section Defs

variable {G : Type} [Group G]

abbrev Quo (Gi : Subgroup G) : Type := ↥Gi ⧸ CFSG.pCore 2 ↥Gi

abbrev mkO2 (Gi : Subgroup G) : ↥Gi →* Quo Gi := QuotientGroup.mk' (CFSG.pCore 2 ↥Gi)

end Defs

section Basic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_two_pow_of_mkO2_eq_one {Gi : Subgroup G} (x : ↥Gi) (hx : mkO2 Gi x = 1) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : x ∈ CFSG.pCore 2 ↥Gi := (QuotientGroup.eq_one_iff x).1 hx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Gi)) ⟨x, hmem⟩
  exact ⟨k, congrArg Subtype.val hk⟩

omit [Finite G] in
theorem orderOf_mkO2_eq_three {Gi : Subgroup G} (x : ↥Gi) (hx : orderOf x = 3) :
    orderOf (mkO2 Gi x) = 3 := by
  apply orderOf_eq_prime
  · rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  · intro h
    obtain ⟨k, hk⟩ := exists_two_pow_of_mkO2_eq_one x h
    have hdvd : 3 ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

omit [Finite G] in
theorem le_of_commutators_mem {L : Subgroup G} (hL : IsShort2 L) (h5 : IsAltType L 5) {y : G}
    (hy : y ∈ L) (hy3 : orderOf y = 3) {N : Subgroup G}
    (hN : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ N) : L ≤ N := by
  obtain ⟨α, hα, hαk, -⟩ := h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαy : α ⟨y, hy⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨y, hy⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := hαk ▸ (MonoidHom.mem_ker.2 h1)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hmem⟩
    have hk' : (⟨y, hy⟩ : ↥L) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hy2k : y ^ 2 ^ k = 1 := congrArg Subtype.val hk'
    have hdvd : 3 ∣ 2 ^ k := hy3 ▸ orderOf_dvd_of_pow_eq_one hy2k
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hshort : ∀ M : Subgroup ↥L, M.Normal → M ⊔ α.ker = ⊤ → M = ⊤ := fun M hM hsup => by
    have : M.Normal := hM
    rw [hαk] at hsup
    exact C1GN.isShort2_eq_top_of_sup_pCore hL M hsup
  have htop := eq_top_of_commutators_mem α hα hshort hαy (N := N.comap L.subtype)
    (fun l => hN l l.2)
  intro l hl
  have : (⟨l, hl⟩ : ↥L) ∈ N.comap L.subtype := htop ▸ Subgroup.mem_top _
  exact this

theorem le_of_modO2Image_le {Gi L K : Subgroup G} (hK : K ∈ cComp Gi) (hLGi : L ≤ Gi)
    (hLperf : ⁅L, L⁆ = L) (hle : modO2Image Gi L ≤ modO2Image Gi K) : L ≤ K := by
  have hLY : L ≤ K ⊔ pCoreOf 2 Gi := fun x hx =>
    P134.mem_sup_of_mem_modO2Image (hLGi hx) (hle (P134.mk_mem_modO2Image hx (hLGi hx)))
  have hKY : K ≤ K ⊔ pCoreOf 2 Gi := le_sup_left
  have hnorm : (K.subgroupOf (K ⊔ pCoreOf 2 Gi)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKY]
    exact sup_le Subgroup.le_normalizer (P134.pCoreOf_le_normalizer_of_mem_cComp hK)
  have h1 : perfectCore (K ⊔ pCoreOf 2 Gi) ≤ K :=
    perfectCore_le_of_sup_solvable hKY hnorm rfl (isSolvable_pCoreOf_two Gi)
  exact (le_perfectCore_of_perfect hLY hLperf).trans h1

omit [Finite G] in
theorem mem_map_comap_mkO2 {Gi : Subgroup G} {N : Subgroup (Quo Gi)} {g : G} :
    g ∈ (N.comap (mkO2 Gi)).map Gi.subtype ↔ ∃ hg : g ∈ Gi, mkO2 Gi ⟨g, hg⟩ ∈ N := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

omit [Finite G] in
theorem perfect_modO2Image {Gi L : Subgroup G} (hLGi : L ≤ Gi) (hLperf : ⁅L, L⁆ = L) :
    ⁅modO2Image Gi L, modO2Image Gi L⁆ = modO2Image Gi L := by
  have h1 : ⁅L.subgroupOf Gi, L.subgroupOf Gi⁆ = L.subgroupOf Gi := by
    apply Subgroup.map_injective Gi.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hLGi, hLperf]
  unfold modO2Image
  rw [← Subgroup.map_commutator, h1]

end Basic

section Main

variable {G : Type} [Group G] [Finite G] {Gi L SI U : Subgroup G}

theorem mkO2_mem_normalizer_modO2Image (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (S : Setting Gi L SI U) {K : Subgroup G} (hK : K ∈ cComp Gi) {z : G} (hz : z ∈ Gi)
    (hodd : Odd (orderOf z)) :
    mkO2 Gi ⟨z, hz⟩ ∈ Subgroup.normalizer (modO2Image Gi K : Set (Quo Gi)) := by
  have hKGi : K ≤ Gi := le_of_mem_cComp hK
  have hK1 : K ∈ conjSubgroupsBy Gi K := ⟨1, Gi.one_mem, by ext x; simp⟩
  have h3 := lemma_1_2_1_three S.qtke h37 h38 S.gi_core hK
  have hzN : z ∈ Subgroup.normalizer (K : Set G) :=
    odd_mem_normalizer_conjSubgroupsBy1516 hKGi (h3.imp_right And.left) hz hodd hK1
  have hzN' : (⟨z, hz⟩ : ↥Gi) ∈ Subgroup.normalizer ((K.subgroupOf Gi : Subgroup ↥Gi) : Set ↥Gi) :=
    (mem_normalizer_subgroupOf_iff' hKGi ⟨z, hz⟩).2 hzN
  exact Subgroup.le_normalizer_map (mkO2 Gi) ⟨_, hzN', rfl⟩

theorem exists_cComp_of_order_three (h36 : A36ForSQTKCat) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (S : Setting Gi L SI U) {y : G} (hyGi : y ∈ Gi)
    (hy3 : orderOf y = 3) (hyL : ∀ l ∈ L, y * l = l * y) : ∃ K ∈ cComp Gi, L ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLperf : ⁅L, L⁆ = L := perfect_of_mem_cComp (L_mem_cComp S)
  have hLGi : L ≤ Gi := S.L_le
  have hQ := sqtkHypCat_quotient_of_pCoreOf_ne_bot S.qtke S.gi_core
  have hFin : Finite (Quo Gi) := hQ.finite
  obtain ⟨y₁, hy₁L, hy₁3⟩ : ∃ y₁ ∈ L, orderOf y₁ = 3 := by
    obtain ⟨α, hα, hαk, -⟩ := S.alt5
    obtain ⟨c, hc⟩ := exists_order_three_alt5
    obtain ⟨z, hz⟩ := hα c
    have hker : ∀ w : ↥L, α w = 1 → ∃ k : ℕ, w ^ 2 ^ k = 1 := by
      intro w hw
      have hmem : w ∈ CFSG.pCore 2 ↥L := hαk ▸ (MonoidHom.mem_ker.2 hw)
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨w, hmem⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    obtain ⟨w, hw3, -⟩ := exists_order_three_lift α hker hc hz
    exact ⟨w, w.2, (Subgroup.orderOf_coe w).trans hw3⟩
  have hy₁G : y₁ ∈ Gi := hLGi hy₁L
  have hodd3 : Odd (3 : ℕ) := ⟨1, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Quo Gi, a = mkO2 Gi ⟨y₁, hy₁G⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Quo Gi, b = mkO2 Gi ⟨y, hyGi⟩ := ⟨_, rfl⟩
  have ha3 : orderOf a = 3 := by
    rw [ha]; exact orderOf_mkO2_eq_three _ (by rw [Subgroup.orderOf_mk]; exact hy₁3)
  have hb3 : orderOf b = 3 := by
    rw [hb]; exact orderOf_mkO2_eq_three _ (by rw [Subgroup.orderOf_mk]; exact hy3)
  have haL : a ∈ modO2Image Gi L := by rw [ha]; exact P134.mk_mem_modO2Image hy₁L hy₁G
  have hab : a * b = b * a := by
    rw [ha, hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyL y₁ hy₁L).symm
  have hbL : ∀ l ∈ modO2Image Gi L, l * b = b * l := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyL g hg).symm
  have hcomm : ∀ K ∈ cComp (⊤ : Subgroup (Quo Gi)), ∀ K' ∈ cComp (⊤ : Subgroup (Quo Gi)), K ≠ K' →
      ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
    intro K hK K' hK' hne k hk k' hk'
    have h := h37 _ hQ K hK K' hK' hne
    have hle : K ≤ Subgroup.centralizer (K' : Set (Quo Gi)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    exact (Subgroup.mem_centralizer_iff.1 (hle hk) k' hk').symm
  have hLbperf : ⁅modO2Image Gi L, modO2Image Gi L⁆ = modO2Image Gi L :=
    perfect_modO2Image hLGi hLperf
  have hLJ : modO2Image Gi L ≤ sSup (cComp (⊤ : Subgroup (Quo Gi))) := by
    have h39' := (h39 _ hQ).1
    have : modO2Image Gi L ≤ perfectCore (⊤ : Subgroup (Quo Gi)) :=
      le_perfectCore_of_perfect le_top hLbperf
    rw [← h39'] at this
    exact this
  have hanorm : ∀ K ∈ cComp (⊤ : Subgroup (Quo Gi)),
      a ∈ Subgroup.normalizer (K : Set (Quo Gi)) := by
    intro K hK
    obtain ⟨K₀, hK₀, rfl⟩ := exists_cComp_modO2Image_eq hK
    rw [ha]
    exact mkO2_mem_normalizer_modO2Image h37 h38 S hK₀ hy₁G (by rw [hy₁3]; exact hodd3)
  have hbnorm : ∀ K ∈ cComp (⊤ : Subgroup (Quo Gi)),
      b ∈ Subgroup.normalizer (K : Set (Quo Gi)) := by
    intro K hK
    obtain ⟨K₀, hK₀, rfl⟩ := exists_cComp_modO2Image_eq hK
    rw [hb]
    exact mkO2_mem_normalizer_modO2Image h37 h38 S hK₀ hyGi (by rw [hy3]; exact hodd3)
  have hB : ∀ x ∈ Subgroup.zpowers a, x ≠ 1 → ∀ N : Subgroup (Quo Gi),
      (∀ l ∈ modO2Image Gi L, l * x * l⁻¹ * x⁻¹ ∈ N) → modO2Image Gi L ≤ N := by
    intro x hx hx1 N hN
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hzL : y₁ ^ m ∈ L := Subgroup.zpow_mem _ hy₁L m
    have hzG : y₁ ^ m ∈ Gi := hLGi hzL
    have hxz : mkO2 Gi ⟨y₁ ^ m, hzG⟩ = a ^ m := by
      rw [ha]
      exact map_zpow (mkO2 Gi) (⟨y₁, hy₁G⟩ : ↥Gi) m
    have hz1 : y₁ ^ m ≠ 1 := by
      intro h
      apply hx1
      rw [← hxz, show (⟨y₁ ^ m, hzG⟩ : ↥Gi) = 1 from Subtype.ext h, map_one]
    have hz3 : orderOf (y₁ ^ m) = 3 := by
      have hdvd : orderOf (y₁ ^ m) ∣ 3 := by
        rw [← hy₁3]
        exact orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers y₁ m)
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hz1
      · exact h
    have hcomm' : ∀ l ∈ L, l * y₁ ^ m * l⁻¹ * (y₁ ^ m)⁻¹ ∈ (N.comap (mkO2 Gi)).map Gi.subtype := by
      intro l hl
      have hlG : l ∈ Gi := hLGi hl
      have hmem : l * y₁ ^ m * l⁻¹ * (y₁ ^ m)⁻¹ ∈ Gi :=
        Gi.mul_mem (Gi.mul_mem (Gi.mul_mem hlG hzG) (Gi.inv_mem hlG)) (Gi.inv_mem hzG)
      refine mem_map_comap_mkO2.2 ⟨hmem, ?_⟩
      have e : (⟨l * y₁ ^ m * l⁻¹ * (y₁ ^ m)⁻¹, hmem⟩ : ↥Gi) =
          ⟨l, hlG⟩ * ⟨y₁ ^ m, hzG⟩ * ⟨l, hlG⟩⁻¹ * ⟨y₁ ^ m, hzG⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hxz]
      exact hN _ (P134.mk_mem_modO2Image hl hlG)
    have hLN₀ : L ≤ (N.comap (mkO2 Gi)).map Gi.subtype :=
      le_of_commutators_mem S.short S.alt5 hzL hz3 hcomm'
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hgG, hgN⟩ := mem_map_comap_mkO2.1 (hLN₀ hg)
    exact hgN
  have hbna : b ∉ Subgroup.zpowers a := by
    intro hbz
    have hb1 : b ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hb3
      omega
    have := hB b hbz hb1 ⊥ (fun l hl => by
      rw [Subgroup.mem_bot, hbL l hl]
      group)
    have ha1 : a = 1 := Subgroup.mem_bot.1 (this haL)
    rw [ha1, orderOf_one] at ha3
    omega
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup (Quo Gi)) ≤ 2 := by
    have := hQ.sqt 3 Nat.prime_three (by norm_num)
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at this
  have hrank := hrank_of_pRank hr ha3 hb3 hab hbna
  have hR : ∀ a' b' c' : Quo Gi, orderOf a' = 3 → orderOf b' = 3 → a' * b' = b' * a' →
      b' ∉ Subgroup.zpowers a' → orderOf c' = 3 → c' * a' = a' * c' → c' * b' = b' * c' →
      ∃ i j : ℕ, c' = a' ^ i * b' ^ j :=
    fun a' b' c' ha' hb' hab' hba' hc' hca' hcb' =>
      hrank_of_pRank hr ha' hb' hab' hba' c' hc' hca' hcb'
  have hdeg : ∀ K₁ ∈ cComp (⊤ : Subgroup (Quo Gi)), ∀ K₂ ∈ cComp (⊤ : Subgroup (Quo Gi)),
      K₁ ≠ K₂ → b ∈ K₁ → b ∈ K₂ → False := by
    intro K₁ hK₁ K₂ hK₂ hne hb₁ hb₂
    exact false_of_shared_central_three hR (perfect_of_mem_cComp hK₁) (perfect_of_mem_cComp hK₂)
      (hcomm K₁ hK₁ K₂ hK₂ hne)
      (fun E hEK hcen hE => card_le_three_of_central_elemAbelian h36 hQ hK₁ hEK hcen hE) hb3 hb₁
      hb₂
  obtain ⟨Kb, hKb, hLKb⟩ := exists_mem_of_commuting hcomm hLJ hLbperf haL ha3 hb3 hab hbL hanorm
    hbnorm hB hdeg hrank
  obtain ⟨K, hK, rfl⟩ := exists_cComp_modO2Image_eq hKb
  exact ⟨K, hK, le_of_modO2Image_le hK hLGi hLperf hLKb⟩

end Main

end CFSG.QuasithinUnique.A5.C25
