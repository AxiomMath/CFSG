module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PC
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem false_of_A_le_sup_cMHat {T R A L : Subgroup X} (hA : AConfig T R A) (hL : IsC2 L)
    (hLn : L.Normal) (hZ : Subgroup.center ↥(barO2 L) = ⊥) (hm3 : 2 ≤ CFSG.Open.pRank 3 L)
    (hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) (hAL : A ⊓ L = ⊥) (hle : A ≤ L ⊔ cMHat L) :
    False := by
  have _ := hL
  haveI := hLn
  have h3 : (3 : ℕ).Prime := Nat.prime_three
  have h32 : (3 : ℕ) ≠ 2 := by norm_num
  have h31 : 1 < 3 := by norm_num
  let q : X →* X ⧸ L := QuotientGroup.mk' L
  have hAq : 2 ≤ CFSG.Open.pRank 3 (A.map q) := by
    obtain ⟨e, -⟩ := autData_conjNormal_aux_equiv q
      (by rw [QuotientGroup.ker_mk']; exact hAL)
    have hcard : Nat.card (A.map q) = 3 ^ 2 :=
      (Nat.card_congr e.toEquiv).symm.trans (hA.card_eq.trans (by norm_num))
    exact CFSG.SectionRank.le_pRank h31 le_rfl
      (CFSG.SectionRank.isElemAbelian_map hA.elemAbelian q) hcard
  have hAC : A.map q ≤ (cMHat L).map q := by
    have h1 : A.map q ≤ (L ⊔ cMHat L).map q := Subgroup.map_mono hle
    rw [Subgroup.map_sup] at h1
    have h2 : L.map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [h2, bot_sup_eq] at h1
  have hC2 : 2 ≤ CFSG.Open.pRank 3 (cMHat L) :=
    two_le_pRank_of_map q h3 h32 (cMHat L) (hAq.trans (CFSG.SectionRank.pRank_mono h31 hAC))
  have hCbar : 2 ≤ CFSG.Open.pRank 3 (cMBar L) := by
    have h1 := pRank_barO2_eq_aux_eq (cMHat L) h3 h32
    have h2 : barO2 (cMHat L) = cMBar L :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) (cMBar L)
    rw [h2] at h1
    omega
  have hLbar : 2 ≤ CFSG.Open.pRank 3 (barO2 L) := by
    have := pRank_barO2_eq_aux_eq L h3 h32
    omega
  have hcomm : ∀ a ∈ barO2 L, ∀ b ∈ cMBar L, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb a ha
  have hinf : barO2 L ⊓ cMBar L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxz : (⟨x, hx.1⟩ : ↥(barO2 L)) ∈ Subgroup.center ↥(barO2 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g.1 g.2 x hx.2)
    rw [hZ, Subgroup.mem_bot] at hxz
    have hx1 : x = 1 := congrArg Subtype.val hxz
    simp [hx1]
  have hrank := pRank_add_le_pRank_sup_add_pRank_inf hcomm h3
  rw [hinf] at hrank
  have hbot : CFSG.Open.pRank 3 (⊥ : Subgroup (X ⧸ CFSG.pCore 2 X)) = 0 := by
    apply Nat.le_zero.1
    refine CFSG.SectionRank.pRank_le h31 (fun E hE _ => ?_)
    rw [le_bot_iff.1 hE]
    simp
  have htop : CFSG.Open.pRank 3 (barO2 L ⊔ cMBar L) ≤ 3 := by
    have h1 := pRank_barO2_eq_aux_eq (⊤ : Subgroup X) h3 h32
    have h2 : barO2 (⊤ : Subgroup X) = ⊤ :=
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [h2] at h1
    calc CFSG.Open.pRank 3 (barO2 L ⊔ cMBar L)
        ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) :=
          CFSG.SectionRank.pRank_mono h31 le_top
      _ ≤ 3 := by omega
  omega

theorem exists_k21dData_aux_isPGroup_comap {G H : Type*} [Group G] [Group H] (ρ : G →* H)
    {N₀ : Subgroup G} (hker : ∀ x ∈ N₀, ρ x = 1 → ∃ j : ℕ, x ^ 2 ^ j = 1)
    {Q : Subgroup H} (hQ : IsPGroup 2 Q) : IsPGroup 2 ↥(N₀ ⊓ Q.comap ρ) := by
  rintro ⟨g, hgN, hgQ⟩
  obtain ⟨k, hk⟩ := hQ ⟨ρ g, hgQ⟩
  have hk' : (ρ g) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := hker (g ^ 2 ^ k) (N₀.pow_mem hgN _) (by rw [map_pow]; exact hk')
  refine ⟨k + j, Subtype.ext ?_⟩
  simpa [pow_add, pow_mul] using hj

theorem exists_k21dData_aux_pCoreOf_normalizes {G : Type*} [Group G] (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H : Subgroup G) : Set G) := by
  have key : ∀ g ∈ H, ∀ x ∈ CFSG.Open.pCoreOf 2 H, g * x * g⁻¹ ∈ CFSG.Open.pCoreOf 2 H := by
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹,
      (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem x hx ⟨g, hg⟩, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have := key g⁻¹ (H.inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem exists_k21dData_aux_isPGroup_pCoreOf {G : Type*} [Group G] (H : Subgroup G) :
    IsPGroup 2 (CFSG.Open.pCoreOf 2 H) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype

theorem exists_k21dData_aux_le_pCoreOf {G : Type*} [Group G] {H P : Subgroup G} (hPH : P ≤ H)
    (hn : H ≤ Subgroup.normalizer (P : Set G)) (hp : IsPGroup 2 P) :
    P ≤ CFSG.Open.pCoreOf 2 H := by
  have hN : (P.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr hn
  have hP2 : IsPGroup 2 (P.subgroupOf H) := hp.comap_subtype
  have h1 : P.subgroupOf H ≤ CFSG.pCore 2 H := le_sSup ⟨hN, hP2⟩
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hPH] at h2

theorem exists_k21dData_aux_max {G H : Type} [Group G] [Group H] (ρ : G →* H)
    {A R N₁ : Subgroup G} (hmax : IsMaxInvariantTwo A R) (hAN : A ≤ N₁) (hRN : R ≤ N₁)
    (hker : ∀ x ∈ N₁, ρ x = 1 → ∃ j : ℕ, x ^ 2 ^ j = 1) {Q : Subgroup H} (hQ : IsPGroup 2 Q)
    (hRQ : R.map ρ ≤ Q) (hAQ : ∀ a ∈ A, ρ a ∈ Subgroup.normalizer (Q : Set H)) :
    N₁ ⊓ Q.comap ρ = R := by
  refine hmax.2.2 _ (exists_k21dData_aux_isPGroup_comap ρ hker hQ) ?_ ?_
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have haN : a ∈ N₁ := hAN ha
    have hρ := Subgroup.mem_normalizer_iff.1 (hAQ a ha) (ρ h)
    constructor
    · rintro ⟨hh, hhQ⟩
      refine ⟨N₁.mul_mem (N₁.mul_mem haN hh) (N₁.inv_mem haN), ?_⟩
      show ρ (a * h * a⁻¹) ∈ Q
      rw [map_mul, map_mul, map_inv]
      exact hρ.1 hhQ
    · rintro ⟨hh, hhQ⟩
      refine ⟨?_, ?_⟩
      · have := N₁.mul_mem (N₁.mul_mem (N₁.inv_mem haN) hh) haN
        simpa [mul_assoc] using this
      · show ρ h ∈ Q
        have hq : ρ (a * h * a⁻¹) ∈ Q := hhQ
        rw [map_mul, map_mul, map_inv] at hq
        exact hρ.2 hq
  · intro r hr
    exact ⟨hRN hr, hRQ ⟨r, hr, rfl⟩⟩

theorem exists_k21dData_aux_pushdown {G H : Type} [Group G] [Group H] (ρ : G →* H)
    {A R N₀ : Subgroup G} (hmax : IsMaxInvariantTwo A R) (hAN : A ≤ N₀) (hRN : R ≤ N₀)
    (hker : ∀ x ∈ N₀, ρ x = 1 → ∃ j : ℕ, x ^ 2 ^ j = 1)
    (hsolv : Group.IsSolvable ↥(Subgroup.normalizer (R : Set G))) :
    R.map ρ = CFSG.Open.pCoreOf 2
        (N₀.map ρ ⊓ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H)) ∧
      Group.IsSolvable ↥(N₀.map ρ ⊓ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H)) := by
  have hR2 : IsPGroup 2 (R.map ρ) := hmax.1.map ρ
  have hAnorm : ∀ a ∈ A, ρ a ∈ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H) :=
    fun a ha => Subgroup.le_normalizer_map ρ ⟨a, hmax.2.1 ha, rfl⟩
  have hF : ∀ x ∈ N₀, ρ x ∈ R.map ρ → x ∈ R := by
    intro x hx hxR
    have h := exists_k21dData_aux_max ρ hmax hAN hRN hker hR2 le_rfl hAnorm
    have : x ∈ N₀ ⊓ (R.map ρ).comap ρ := ⟨hx, hxR⟩
    rwa [h] at this
  have hfwd : ∀ x ∈ N₀, ρ x ∈ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H) →
      ∀ r ∈ R, x * r * x⁻¹ ∈ R := by
    intro x hx hρx r hr
    refine hF _ (N₀.mul_mem (N₀.mul_mem hx (hRN hr)) (N₀.inv_mem hx)) ?_
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hρx (ρ r)).1 ⟨r, hr, rfl⟩
  have hK : ∀ x ∈ N₀, ρ x ∈ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H) →
      x ∈ Subgroup.normalizer (R : Set G) := by
    intro x hx hρx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hfwd x hx hρx h hh, fun hh => ?_⟩
    have := hfwd x⁻¹ (N₀.inv_mem hx) (by rw [map_inv]; exact Subgroup.inv_mem _ hρx) _ hh
    simpa [mul_assoc] using this
  have h𝒩R : ∀ y ∈ N₀.map ρ ⊓ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H),
      ∃ x ∈ N₀ ⊓ Subgroup.normalizer (R : Set G), ρ x = y := by
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, hK x hx hy⟩, rfl⟩
  have hR𝒩 : R.map ρ ≤ N₀.map ρ ⊓ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H) := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨⟨r, hRN hr, rfl⟩, Subgroup.le_normalizer ⟨r, hr, rfl⟩⟩
  have hle : R.map ρ ≤ CFSG.Open.pCoreOf 2
      (N₀.map ρ ⊓ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H)) :=
    exists_k21dData_aux_le_pCoreOf hR𝒩 inf_le_right hR2
  refine ⟨le_antisymm hle ?_, ?_⟩
  · have hQ2 := exists_k21dData_aux_isPGroup_pCoreOf
      (N₀.map ρ ⊓ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H))
    have hQnorm := exists_k21dData_aux_pCoreOf_normalizes
      (N₀.map ρ ⊓ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H))
    have hAN₁ : A ≤ N₀ ⊓ Subgroup.normalizer (R : Set G) := le_inf hAN hmax.2.1
    have hRN₁ : R ≤ N₀ ⊓ Subgroup.normalizer (R : Set G) := le_inf hRN Subgroup.le_normalizer
    have hker₁ : ∀ x ∈ N₀ ⊓ Subgroup.normalizer (R : Set G), ρ x = 1 → ∃ j : ℕ, x ^ 2 ^ j = 1 :=
      fun x hx => hker x hx.1
    have hmaxQ := exists_k21dData_aux_max ρ hmax hAN₁ hRN₁ hker₁ hQ2 hle (fun a ha =>
      hQnorm ⟨⟨a, hAN ha, rfl⟩, hAnorm a ha⟩)
    intro y hy
    obtain ⟨x, hx, rfl⟩ := h𝒩R y (Subgroup.map_subtype_le _ hy)
    have hxR : x ∈ (N₀ ⊓ Subgroup.normalizer (R : Set G)) ⊓
        (CFSG.Open.pCoreOf 2
          (N₀.map ρ ⊓ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H))).comap ρ :=
      ⟨hx, hy⟩
    rw [hmaxQ] at hxR
    exact ⟨x, hxR, rfl⟩
  · haveI := hsolv
    haveI : Group.IsSolvable ↥((Subgroup.normalizer (R : Set G)).map ρ) :=
      Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
    have hsub : N₀.map ρ ⊓ Subgroup.normalizer ((R.map ρ : Subgroup H) : Set H) ≤
        (Subgroup.normalizer (R : Set G)).map ρ := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := h𝒩R y hy
      exact ⟨x, hx.2, rfl⟩
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hsub)

theorem exists_k21dData_aux_R_le {T R A : Subgroup X} (hA : AConfig T R A)
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) : R ≤ T := by
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hT.1, hT.2.1, hT.2.2⟩
  have h2 : CFSG.ABGLocalTools.IsSylowOf 2 T (A ⊔ T) := hSyl.of_le le_sup_right le_top
  have h3 : CFSG.QuasithinUnique.IsSylowTwoOf T (A ⊔ T) := CFSG.ABGLocalTools.isSylowOf_iff.mp h2
  rw [hA.core]
  exact CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf h3

theorem exists_k21dData_aux_ker {L T : Subgroup X} (hLn : L.Normal) (hT2 : IsPGroup 2 T)
    (hZ : Subgroup.center ↥(barO2 L) = ⊥) {x : X} (hx : x ∈ L ⊔ T)
    (hxc : QuotientGroup.mk' (CFSG.pCore 2 X) x ∈
      Subgroup.centralizer ((barO2 L : Subgroup (X ⧸ CFSG.pCore 2 X)) : Set (X ⧸ CFSG.pCore 2 X))) :
    ∃ j : ℕ, x ^ 2 ^ j = 1 := by
  haveI := hLn
  let q : X →* X ⧸ L := QuotientGroup.mk' L
  have hqx : q x ∈ T.map q := by
    have h1 : q x ∈ (L ⊔ T).map q := ⟨x, hx, rfl⟩
    rw [Subgroup.map_sup] at h1
    have h2 : L.map q = ⊥ := by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [h2, bot_sup_eq] at h1
  obtain ⟨k, hk⟩ := (hT2.map q) ⟨q x, hqx⟩
  have hk' : (q x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hxk : x ^ 2 ^ k ∈ L := by
    rw [← QuotientGroup.ker_mk' L]
    exact MonoidHom.mem_ker.2 (by rw [map_pow]; exact hk')
  have hπz : QuotientGroup.mk' (CFSG.pCore 2 X) (x ^ 2 ^ k) ∈
      Subgroup.centralizer ((barO2 L : Subgroup (X ⧸ CFSG.pCore 2 X)) : Set (X ⧸ CFSG.pCore 2 X)) := by
    rw [map_pow]
    exact Subgroup.pow_mem _ hxc _
  have hzL : QuotientGroup.mk' (CFSG.pCore 2 X) (x ^ 2 ^ k) ∈ barO2 L := ⟨x ^ 2 ^ k, hxk, rfl⟩
  have hcen : (⟨_, hzL⟩ : ↥(barO2 L)) ∈ Subgroup.center ↥(barO2 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hπz g.1 g.2)
  rw [hZ, Subgroup.mem_bot] at hcen
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) (x ^ 2 ^ k) = 1 := congrArg Subtype.val hcen
  have hzp : x ^ 2 ^ k ∈ CFSG.pCore 2 X := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 X)]
    exact h1
  obtain ⟨j, hj⟩ := pRank_barO2_eq_aux_powTwo hzp
  exact ⟨k + j, by rw [pow_add, pow_mul]; exact hj⟩

theorem exists_k21dData {T R A L : Subgroup X} (hA : AConfig T R A)
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hL : IsC2 L) (hLn : L.Normal)
    (hZ : Subgroup.center ↥(barO2 L) = ⊥) (hAL : A ≤ L) (hnc : ⁅barO2 L, barO2 A⁆ ≠ ⊥) :
    ∃ N T' R' E : Subgroup (MulAut ↥(barO2 L)), K21dData ↥(barO2 L) N T' R' E := by
  have _ := hL
  haveI : (L.map (QuotientGroup.mk' (CFSG.pCore 2 X))).Normal :=
    Subgroup.Normal.map hLn _ (QuotientGroup.mk'_surjective _)
  set π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X)
  set ρ : X →* MulAut ↥(L.map π) :=
    (MulAut.conjNormal : (X ⧸ CFSG.pCore 2 X) →* MulAut ↥(L.map π)).comp π
  have hAut := autData_conjNormal π hLn hA hT hnc
  have hRT : R ≤ T := exists_k21dData_aux_R_le hA hT
  have hkerρ : ρ.ker = (Subgroup.centralizer ((L.map π : Subgroup (X ⧸ CFSG.pCore 2 X)) :
      Set (X ⧸ CFSG.pCore 2 X))).comap π := ker_conjNormal_comp π
  have hker : ∀ x ∈ L ⊔ T, ρ x = 1 → ∃ j : ℕ, x ^ 2 ^ j = 1 := by
    intro x hx hρx
    refine exists_k21dData_aux_ker hLn hT.2.1 hZ hx ?_
    have h1 : x ∈ ρ.ker := hρx
    rw [hkerρ] at h1
    exact h1
  have hAN : A ≤ L ⊔ T := hAL.trans le_sup_left
  have hRN : R ≤ L ⊔ T := hRT.trans le_sup_right
  obtain ⟨hcore, hsolv⟩ := exists_k21dData_aux_pushdown ρ hA.maximal hAN hRN hker hA.solvable
  refine ⟨(L ⊔ T).map ρ, T.map ρ, R.map ρ, A.map ρ, ?_⟩
  refine ⟨?_, Subgroup.map_mono le_sup_right, hAut.pgroup, hAut.sylow, Subgroup.map_mono hRT, ?_,
    hcore, hsolv, ?_, hAut.elemAbelian, hAut.card_eq, hAut.quaternion⟩
  · rintro _ ⟨k, rfl⟩
    obtain ⟨j, hj, hjk⟩ := k.2
    refine ⟨j, Subgroup.mem_sup_left hj, ?_⟩
    show MulAut.conjNormal (π j) = MulAut.conj k
    have h1 : π j = (k : X ⧸ CFSG.pCore 2 X) := hjk
    rw [h1, MulAut.conjNormal_val]
  · have hTN : T ≤ Subgroup.normalizer (R : Set X) := by
      rw [hA.core]
      exact le_sup_right.trans (exists_k21dData_aux_pCoreOf_normalizes (A ⊔ T))
    rintro _ ⟨t, ht, rfl⟩
    exact Subgroup.le_normalizer_map ρ ⟨t, hTN ht, rfl⟩
  · refine le_inf (Subgroup.map_mono hAN) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.le_normalizer_map ρ ⟨a, hA.maximal.2.1 ha, rfl⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
