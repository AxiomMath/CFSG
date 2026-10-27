module

public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCoreZ
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem closureIn_eq_sSup (I H : Subgroup G) :
    closureIn I H = sSup {X | ∃ g ∈ H, X = GLBConj g I} := by
  rw [closureIn_eq_iSup_gLBConj]
  apply le_antisymm
  · exact iSup₂_le fun g hg => le_sSup ⟨g, hg, rfl⟩
  · exact sSup_le fun X ⟨g, hg, hX⟩ => hX ▸ le_biSup (fun g => GLBConj g I) hg

private theorem mem_normalizer_sSup_of_perm {S : Set (Subgroup G)} {g : G}
    (h1 : ∀ X ∈ S, GLBConj g X ∈ S) (h2 : ∀ X ∈ S, GLBConj g⁻¹ X ∈ S) :
    g ∈ Subgroup.normalizer ((sSup S : Subgroup G) : Set G) := by
  have key : ∀ g' : G, (∀ X ∈ S, GLBConj g' X ∈ S) → GLBConj g' (sSup S) ≤ sSup S := by
    intro g' hg'
    unfold GLBConj
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun X hX => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hg' X hX)
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key g h1) ?_
  have h' := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono g (key g⁻¹ h2)
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h'

private theorem mem_normalizer_inf {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at *
  rw [gLBConj_inf, hX, hY]

private def cmSub (N Z : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (N : Set G) ∧ ∀ z ∈ Z, ⁅z, g⁆ ∈ N}
  one_mem' := ⟨Subgroup.one_mem _, fun z _ => by
    rw [commutatorElement_one_right]
    exact N.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, hZa⟩ ⟨hb, hZb⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun z hz => ?_⟩
    rw [commutatorElement_mul_right]
    exact N.mul_mem (hZa z hz) ((Subgroup.mem_normalizer_iff.1 ha _).1 (hZb z hz))
  inv_mem' := by
    rintro a ⟨ha, hZa⟩
    refine ⟨Subgroup.inv_mem _ ha, fun z hz => ?_⟩
    rw [commutatorElement_inv_right]
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ha) ⁅z, a⁆⁻¹).1
      (N.inv_mem (hZa z hz))
    simpa [inv_inv] using this

private theorem commutator_le_of_forall_gen {N X : Subgroup G} {𝒴 : Set (Subgroup G)}
    (h𝒴 : ∀ Y ∈ 𝒴, Y ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ Y ∈ 𝒴, (⁅X, Y⁆ : Subgroup G) ≤ N) : (⁅X, sSup 𝒴⁆ : Subgroup G) ≤ N := by
  have hle : sSup 𝒴 ≤ cmSub N X := sSup_le fun Y hY y hy =>
    ⟨h𝒴 Y hY hy, fun x hx => h Y hY (Subgroup.commutator_mem_commutator hx hy)⟩
  exact Subgroup.commutator_le.2 fun x hx y hy => (hle hy).2 x hx

private theorem commutator_sSup_sSup_le {N : Subgroup G} {𝒳 𝒴 : Set (Subgroup G)}
    (h𝒳 : ∀ X ∈ 𝒳, X ≤ Subgroup.normalizer (N : Set G))
    (h𝒴 : ∀ Y ∈ 𝒴, Y ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ X ∈ 𝒳, ∀ Y ∈ 𝒴, (⁅X, Y⁆ : Subgroup G) ≤ N) :
    (⁅sSup 𝒳, sSup 𝒴⁆ : Subgroup G) ≤ N := by
  refine commutator_le_of_forall_gen h𝒴 fun Y hY => ?_
  rw [Subgroup.commutator_comm]
  exact commutator_le_of_forall_gen h𝒳 fun X hX => by
    rw [Subgroup.commutator_comm]
    exact h X hX Y hY

private theorem commutator_le_of_le_normalizer {N X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) : (⁅X, N⁆ : Subgroup G) ≤ N := by
  refine Subgroup.commutator_le.2 fun x hx n hn => ?_
  have h1 : x * n * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hX hx) n).1 hn
  rw [commutatorElement_def]
  exact N.mul_mem h1 (N.inv_mem hn)

private theorem pow_mul_mem {N : Subgroup G} {t z : G}
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (hz : z ∈ N) (m : ℕ) :
    ∃ z' ∈ N, (t * z) ^ m = t ^ m * z' := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨z', hz', h⟩ := ih
    have htm : t ^ m ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ ht m
    refine ⟨((t ^ m)⁻¹ * z * t ^ m) * z', N.mul_mem ?_ hz', ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ htm) z).1 hz
      simpa using this
    · rw [pow_succ', h]
      group

private theorem not_dvd_card_of_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Subgroup G} (hS : IsPGroup 2 S) : ¬ p ∣ Nat.card S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

private theorem exists_conj_le_map_sylow {Y R : Subgroup G} (S₀ : Sylow 2 ↥Y) (hRY : R ≤ Y)
    (hR : IsPGroup 2 R) :
    ∃ y ∈ Y, R ≤ GLBConj y ((S₀ : Subgroup ↥Y).map Y.subtype) := by
  have hR' : IsPGroup 2 (R.subgroupOf Y) :=
    hR.of_injective (Subgroup.subgroupOfEquivOfLe hRY).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hRY).injective
  obtain ⟨S', hS'⟩ := hR'.exists_le_sylow
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq ↥Y S₀ S'
  refine ⟨((z⁻¹ : ↥Y) : G), (z⁻¹).2, fun r hr => ?_⟩
  rw [mem_gLBConj]
  have hrY : r ∈ Y := hRY hr
  have h1 : (⟨r, hrY⟩ : ↥Y) ∈ (S' : Subgroup ↥Y) := hS' (Subgroup.mem_subgroupOf.2 hr)
  rw [← hz, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨s, hs, hsr⟩ := h1
  refine ⟨s, hs, ?_⟩
  have e : (z : G) * s * (z : G)⁻¹ = r := congrArg Subtype.val hsr
  rw [← e]
  simp [mul_assoc]

private theorem exists_sylow_two_sup_eq {Y Q : Subgroup G} (hQY : Q ≤ Y)
    (hYQ : Y ≤ Subgroup.normalizer (Q : Set G)) (h2 : ∀ y ∈ Y, ∃ n : ℕ, y ^ (2 ^ n) ∈ Q) :
    ∃ S₀ : Sylow 2 ↥Y, (S₀ : Subgroup ↥Y).map Y.subtype ⊔ Q = Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 ↥Y) := inferInstance
  refine ⟨S₀, ?_⟩
  have hQn : (Q.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQY).2 hYQ
  have hpow : IsPGroup 2 (↥Y ⧸ Q.subgroupOf Y) := by
    rw [IsPGroup.iff_orderOf]
    intro g
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨n, hn⟩ := h2 z z.2
    have h1 : (QuotientGroup.mk z : ↥Y ⧸ Q.subgroupOf Y) ^ (2 ^ n) = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 hn
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨k, hk⟩
  obtain ⟨m, hm⟩ := hpow.exists_card_eq
  have hidx : ((S₀ : Subgroup ↥Y) ⊔ Q.subgroupOf Y).index = 1 := by
    have h1 : ((S₀ : Subgroup ↥Y) ⊔ Q.subgroupOf Y).index ∣ (Q.subgroupOf Y).index :=
      Subgroup.index_dvd_of_le le_sup_right
    have h3 : ((S₀ : Subgroup ↥Y) ⊔ Q.subgroupOf Y).index ∣ (S₀ : Subgroup ↥Y).index :=
      Subgroup.index_dvd_of_le le_sup_left
    have h4 : (Q.subgroupOf Y).index = 2 ^ m := hm
    rw [h4] at h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    rcases k with _ | k
    · simpa using hk
    · exfalso
      apply S₀.not_dvd_index
      rw [hk] at h3
      exact (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h3
  have htop : (S₀ : Subgroup ↥Y) ⊔ Q.subgroupOf Y = ⊤ := Subgroup.index_eq_one.1 hidx
  have := congrArg (Subgroup.map Y.subtype) htop
  rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hQY,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this

private theorem exists_invariant_two_subgroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y Q O A : Subgroup G} (hOQ : O ≤ Q) (hQY : Q ≤ Y)
    (hYO : Y ≤ Subgroup.normalizer (O : Set G)) (hYQ : Y ≤ Subgroup.normalizer (Q : Set G))
    (hO : ¬ p ∣ Nat.card O) (hcomm : ∀ q ∈ Q, ∀ y ∈ Y, ⁅q, y⁆ ∈ O)
    (h2 : ∀ y ∈ Y, ∃ n : ℕ, y ^ (2 ^ n) ∈ Q)
    (hAp : IsPGroup p A) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hAO : A ≤ Subgroup.normalizer (O : Set G)) (hnQ : ¬ Y ≤ Q) :
    ∃ S : Subgroup G, S ≤ Y ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      ¬ S ≤ Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀Q⟩ := exists_sylow_two_sup_eq hQY hYQ h2
  obtain ⟨S₁, hS₁def⟩ : ∃ S₁ : Subgroup G, S₁ = (S₀ : Subgroup ↥Y).map Y.subtype := ⟨_, rfl⟩
  rw [← hS₁def] at hS₀Q
  have hS₁Y : S₁ ≤ Y := hS₁def ▸ Subgroup.map_subtype_le _
  have hS₁2 : IsPGroup 2 S₁ := hS₁def ▸ S₀.isPGroup'.map Y.subtype
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = S₁ ⊔ O := ⟨_, rfl⟩
  have hS₁W : S₁ ≤ W := hWdef ▸ le_sup_left
  have hOW : O ≤ W := hWdef ▸ le_sup_right
  have hWY : W ≤ Y := hWdef ▸ sup_le hS₁Y (hOQ.trans hQY)
  have hQW : Q ≤ Subgroup.normalizer (W : Set G) := by
    intro q hq
    apply CFSG.LocalAnalysis.GLTheoremA.mem_normalizer_of_conj_mem
    intro w hw
    have hle : W ≤ W.comap (MulAut.conj q).toMonoidHom := by
      refine hWdef.le.trans (sup_le (fun s hs => ?_) (fun o ho => ?_))
      · show q * s * q⁻¹ ∈ W
        have hc : ⁅q, s⁆ ∈ O := hcomm q hq s (hS₁Y hs)
        have e : q * s * q⁻¹ = ⁅q, s⁆ * s := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact W.mul_mem (hOW hc) (hS₁W hs)
      · show q * o * q⁻¹ ∈ W
        exact hOW ((Subgroup.mem_normalizer_iff.1 (hYO (hQY hq)) o).1 ho)
    exact hle hw
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := by
    rw [← hS₀Q]
    exact sup_le (hS₁W.trans Subgroup.le_normalizer) hQW
  have hR2W : ∀ R : Subgroup G, R ≤ Y → IsPGroup 2 R → R ≤ W := by
    intro R hRY hR
    obtain ⟨y, hy, hRy⟩ := exists_conj_le_map_sylow S₀ hRY hR
    rw [← hS₁def] at hRy
    refine hRy.trans ?_
    calc GLBConj y S₁ ≤ GLBConj y W := CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono y hS₁W
      _ = W := mem_normalizer_iff_gLBConj_eq.1 (hYW hy)
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := by
    intro a ha
    apply CFSG.LocalAnalysis.GLTheoremA.mem_normalizer_of_conj_mem
    intro w hw
    have hle : W ≤ W.comap (MulAut.conj a).toMonoidHom := by
      refine hWdef.le.trans (sup_le (fun s hs => ?_) (fun o ho => ?_))
      · show a * s * a⁻¹ ∈ W
        have hR : GLBConj a⁻¹ S₁ ≤ Y := by
          intro x hx
          have h1 : a⁻¹ * x * a⁻¹⁻¹ ∈ S₁ := mem_gLBConj.1 hx
          have h2 := (Subgroup.mem_normalizer_iff.1 (hAY ha) _).1 (hS₁Y h1)
          have e : a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ = x := by group
          rwa [e] at h2
        refine hR2W _ hR (hS₁2.map _) ?_
        rw [mem_gLBConj]
        have e : a⁻¹ * (a * s * a⁻¹) * a⁻¹⁻¹ = s := by group
        rwa [e]
      · show a * o * a⁻¹ ∈ W
        exact hOW ((Subgroup.mem_normalizer_iff.1 (hAO ha) o).1 ho)
    exact hle hw
  have hWp : ¬ p ∣ Nat.card W := by
    have := not_dvd_card_sup_of_le_normalizer hp (A := O) (B := S₁)
      (fun s hs => hYO (hS₁Y hs)) hO (not_dvd_card_of_isPGroup_two hp hp2 hS₁2)
    rwa [sup_comm, ← hWdef] at this
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_sylow_normalized (r := 2) (p := p)
    hAW hAp hWp
  have hSW : (P : Subgroup ↥W).map W.subtype ≤ W := Subgroup.map_subtype_le _
  refine ⟨(P : Subgroup ↥W).map W.subtype, hSW.trans hWY, P.isPGroup'.map W.subtype, hP,
    fun hSQ => hnQ ?_⟩
  obtain ⟨w, hw, hS₁w⟩ := exists_conj_le_map_sylow P hS₁W hS₁2
  have hwQ : GLBConj w ((P : Subgroup ↥W).map W.subtype) ≤ Q :=
    calc GLBConj w ((P : Subgroup ↥W).map W.subtype) ≤ GLBConj w Q :=
          CFSG.LocalAnalysis.GLTheoremB.gLBConj_mono w hSQ
      _ = Q := mem_normalizer_iff_gLBConj_eq.1 (hYQ (hWY hw))
  rw [← hS₀Q]
  exact sup_le (hS₁w.trans hwQ) le_rfl

theorem exists_two_subgroup_le_closureIn_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {C L A B T : Subgroup G} (hL : GLAPComponent p C L) (hBC : B ≤ C) (hAB : A ≤ B)
    (hAp : IsPGroup p A) (hTK : T ≤ closureIn L B) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hTO : ¬ T ≤ GLAPPrimeCoreOf p C) :
    ∃ S : Subgroup G, S ≤ closureIn L A ⊔ GLAPPrimeCoreOf p C ∧ IsPGroup 2 S ∧
      A ≤ Subgroup.normalizer (S : Set G) ∧ ¬ S ≤ GLAPPrimeCoreOf p C := by
  have hCN : C ≤ Subgroup.normalizer (GLAPPrimeCoreOf p C : Set G) :=
    le_normalizer_glaPPrimeCoreOf p C
  have hOp : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p C) := not_dvd_card_glaPPrimeCoreOf hp C
  set O : Subgroup G := GLAPPrimeCoreOf p C with hOdef
  set 𝓛 : Set (Subgroup G) := {X | ∃ b ∈ B, X = GLBConj b L} with h𝓛def
  set 𝓗 : Set (Subgroup G) := {X | ∃ a ∈ A, X = GLBConj a L} with h𝓗def
  set 𝓜 : Set (Subgroup G) := 𝓛 \ 𝓗 with h𝓜def
  have hconj : ∀ X ∈ 𝓛, GLAPComponent p C X := by
    rintro X ⟨b, hb, rfl⟩
    have h := glaPComponent_gLBConj hL b
    rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBC hb))] at h
  have hLC : ∀ X ∈ 𝓛, X ≤ C := fun X hX => (hconj X hX).1
  have hLH : ∀ X ∈ 𝓗, X ∈ 𝓛 := by
    rintro X ⟨a, ha, rfl⟩
    exact ⟨a, hAB ha, rfl⟩
  have hLmem : L ∈ 𝓗 := ⟨1, A.one_mem, (gLBConj_one L).symm⟩
  have hK : closureIn L B = sSup 𝓛 := closureIn_eq_sSup L B
  have hH : closureIn L A = sSup 𝓗 := closureIn_eq_sSup L A
  have hLHM : sSup 𝓛 = sSup 𝓗 ⊔ sSup 𝓜 := by
    rw [← sSup_union, Set.union_diff_cancel (fun X hX => hLH X hX)]
  have hTKs : T ≤ sSup 𝓛 := hK ▸ hTK
  set H : Subgroup G := sSup 𝓗 with hHdef
  set M : Subgroup G := sSup 𝓜 with hMdef
  have hHC : H ≤ C := sSup_le fun X hX => hLC X (hLH X hX)
  have hMC : M ≤ C := sSup_le fun X hX => hLC X hX.1
  have hOC : O ≤ C := Subgroup.map_subtype_le _
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := fun a ha => hCN (hBC (hAB ha))
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := fun a ha => hBT (hAB ha)
  have hKnorm : ∀ X, GLAPComponent p C X → sSup 𝓛 ≤ Subgroup.normalizer (X : Set G) := by
    intro X hX
    refine sSup_le fun L' hL' => ?_
    by_cases hXL : X = L'
    · subst hXL
      exact Subgroup.le_normalizer
    · intro g hg
      exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp hX (hconj L' hL')
        hXL hg
  have hKH : sSup 𝓛 ≤ Subgroup.normalizer (H : Set G) :=
    fun k hk => mem_normalizer_sSup (fun X hX => hKnorm X (hconj X (hLH X hX)) hk)
  have hKM : sSup 𝓛 ≤ Subgroup.normalizer (M : Set G) :=
    fun k hk => mem_normalizer_sSup (fun X hX => hKnorm X (hconj X hX.1) hk)
  have hHK : H ≤ sSup 𝓛 := hLHM ▸ le_sup_left
  have hHM : H ≤ Subgroup.normalizer (M : Set G) := hHK.trans hKM
  have hperm𝓗 : ∀ a ∈ A, ∀ X ∈ 𝓗, GLBConj a X ∈ 𝓗 := by
    rintro a ha X ⟨a', ha', rfl⟩
    exact ⟨a' * a, A.mul_mem ha' ha, gLBConj_gLBConj a a' L⟩
  have hperm𝓜 : ∀ a ∈ A, ∀ X ∈ 𝓜, GLBConj a X ∈ 𝓜 := by
    rintro a ha X ⟨⟨b, hb, rfl⟩, hX𝓗⟩
    refine ⟨⟨b * a, B.mul_mem hb (hAB ha), gLBConj_gLBConj a b L⟩, fun hmem => hX𝓗 ?_⟩
    have := hperm𝓗 a⁻¹ (A.inv_mem ha) _ hmem
    rwa [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at this
  have hAH : A ≤ Subgroup.normalizer (H : Set G) := fun a ha =>
    mem_normalizer_sSup_of_perm (hperm𝓗 a ha) (hperm𝓗 a⁻¹ (A.inv_mem ha))
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := fun a ha =>
    mem_normalizer_sSup_of_perm (hperm𝓜 a ha) (hperm𝓜 a⁻¹ (A.inv_mem ha))
  have hcommHM : (⁅H, M⁆ : Subgroup G) ≤ O := by
    refine commutator_sSup_sSup_le (fun X hX => (hLC X (hLH X hX)).trans hCN)
      (fun X hX => (hLC X hX.1).trans hCN) fun X hX Y hY => ?_
    exact CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne hp
      (hconj X (hLH X hX)) (hconj Y hY.1) fun h => hY.2 (h ▸ hX)
  have hcommMO : (⁅M ⊔ O, H ⊔ O⁆ : Subgroup G) ≤ O := by
    have := commutator_sSup_sSup_le (N := O) (𝒳 := {M, O}) (𝒴 := {H, O})
      (by
        rintro X (rfl | rfl)
        · exact hMC.trans hCN
        · exact Subgroup.le_normalizer)
      (by
        rintro X (rfl | rfl)
        · exact hHC.trans hCN
        · exact Subgroup.le_normalizer)
      (by
        rintro X (rfl | rfl) Y (rfl | rfl)
        · rw [Subgroup.commutator_comm]
          exact hcommHM
        · exact commutator_le_of_le_normalizer (hMC.trans hCN)
        · rw [Subgroup.commutator_comm]
          exact commutator_le_of_le_normalizer (hHC.trans hCN)
        · exact commutator_le_of_le_normalizer Subgroup.le_normalizer)
    rwa [sSup_pair, sSup_pair] at this
  have hTp : ¬ p ∣ Nat.card T := not_dvd_card_of_isPGroup_two hp hp2 hT2
  have hstep1 : ¬ (⁅T, L⁆ : Subgroup G) ≤ O := by
    intro hTL
    have hb : ∀ b ∈ B, (⁅T, GLBConj b L⁆ : Subgroup G) ≤ O := by
      intro b hb
      refine Subgroup.commutator_le.2 fun t ht y hy => ?_
      have hy' : b * y * b⁻¹ ∈ L := mem_gLBConj.1 hy
      have ht' : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hBT hb) t).1 ht
      have h1 : ⁅b * t * b⁻¹, b * y * b⁻¹⁆ ∈ O :=
        hTL (Subgroup.commutator_mem_commutator ht' hy')
      have e : ⁅b * t * b⁻¹, b * y * b⁻¹⁆ = b * ⁅t, y⁆ * b⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e] at h1
      exact (Subgroup.mem_normalizer_iff.1 (hCN (hBC hb)) _).2 h1
    have hc : (⁅T, sSup 𝓛⁆ : Subgroup G) ≤ O :=
      commutator_le_of_forall_gen (fun X hX => (hLC X hX).trans hCN) (by
        rintro X ⟨b, hb', rfl⟩
        exact hb b hb')
    exact hTO (le_glaPPrimeCoreOf_of_commutator_le hp 𝓛 hconj hTp (hTKs.trans le_sup_left) hc)
  have hTM : T ≤ Subgroup.normalizer (M : Set G) := hTKs.trans hKM
  have hTO' : T ≤ Subgroup.normalizer (O : Set G) :=
    (hTKs.trans (sSup_le fun X hX => hLC X hX)).trans hCN
  have hTN : T ≤ Subgroup.normalizer ((M ⊔ O : Subgroup G) : Set G) :=
    fun t ht => mem_normalizer_sup (hTM ht) (hTO' ht)
  have hHN : H ≤ Subgroup.normalizer ((M ⊔ O : Subgroup G) : Set G) :=
    fun h hh => mem_normalizer_sup (hHM hh) (hCN (hHC hh))
  have hHON : H ⊔ O ≤ Subgroup.normalizer ((M ⊔ O : Subgroup G) : Set G) :=
    sup_le hHN (le_sup_right.trans Subgroup.le_normalizer)
  have hTYM : T ≤ ((H ⊔ O) ⊓ (T ⊔ (M ⊔ O))) ⊔ M := by
    intro t ht
    have htHM : t ∈ H ⊔ M := hLHM ▸ hTKs ht
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H M hHM] at htHM
    obtain ⟨h, hh, m, hm, rfl⟩ := Set.mem_mul.mp htHM
    have hhT : h ∈ T ⊔ (M ⊔ O) := by
      have e : h = h * m * m⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht)
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left (M.inv_mem hm)))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨Subgroup.mem_sup_left hh, hhT⟩)
      (Subgroup.mem_sup_right hm)
  have hnQ : ¬ (H ⊔ O) ⊓ (T ⊔ (M ⊔ O)) ≤ ((H ⊔ O) ⊓ (T ⊔ (M ⊔ O))) ⊓ (M ⊔ O) := by
    intro hYQ
    have hYN : (H ⊔ O) ⊓ (T ⊔ (M ⊔ O)) ≤ M ⊔ O := fun y hy => (hYQ hy).2
    have hTN' : T ≤ M ⊔ O := hTYM.trans (sup_le hYN le_sup_left)
    have hLHO : L ≤ H ⊔ O := (le_sSup hLmem).trans le_sup_left
    exact hstep1 ((Subgroup.commutator_mono hTN' hLHO).trans hcommMO)
  have hOY : O ≤ (H ⊔ O) ⊓ (T ⊔ (M ⊔ O)) :=
    le_inf le_sup_right (le_sup_right.trans le_sup_right)
  have hYO : (H ⊔ O) ⊓ (T ⊔ (M ⊔ O)) ≤ Subgroup.normalizer (O : Set G) :=
    inf_le_left.trans (sup_le (hHC.trans hCN) Subgroup.le_normalizer)
  have hYQ : (H ⊔ O) ⊓ (T ⊔ (M ⊔ O)) ≤
      Subgroup.normalizer ((((H ⊔ O) ⊓ (T ⊔ (M ⊔ O))) ⊓ (M ⊔ O) : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_inf (Subgroup.le_normalizer hy) (hHON hy.1)
  have hAY : A ≤ Subgroup.normalizer (((H ⊔ O) ⊓ (T ⊔ (M ⊔ O)) : Subgroup G) : Set G) :=
    fun a ha => mem_normalizer_inf (mem_normalizer_sup (hAH ha) (hAO ha))
      (mem_normalizer_sup (hAT ha) (mem_normalizer_sup (hAM ha) (hAO ha)))
  have hcomm : ∀ q ∈ ((H ⊔ O) ⊓ (T ⊔ (M ⊔ O))) ⊓ (M ⊔ O),
      ∀ y ∈ (H ⊔ O) ⊓ (T ⊔ (M ⊔ O)), ⁅q, y⁆ ∈ O := fun q hq y hy =>
    hcommMO (Subgroup.commutator_mem_commutator hq.2 hy.1)
  have h2 : ∀ y ∈ (H ⊔ O) ⊓ (T ⊔ (M ⊔ O)),
      ∃ n : ℕ, y ^ (2 ^ n) ∈ ((H ⊔ O) ⊓ (T ⊔ (M ⊔ O))) ⊓ (M ⊔ O) := by
    intro y hy
    have hyTN : y ∈ T ⊔ (M ⊔ O) := hy.2
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right T (M ⊔ O) hTN] at hyTN
    obtain ⟨t, ht, z, hz, rfl⟩ := Set.mem_mul.mp hyTN
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hT2 ⟨t, ht⟩
    have hk' : t ^ (2 ^ k) = 1 := by
      have : orderOf t = 2 ^ k := by rw [← Subgroup.orderOf_mk t ht]; exact hk
      rw [← this]
      exact pow_orderOf_eq_one t
    obtain ⟨z', hz', hpow⟩ := pow_mul_mem (N := M ⊔ O) (hTN ht) hz (2 ^ k)
    refine ⟨k, Subgroup.pow_mem _ hy _, ?_⟩
    rw [hpow, hk', one_mul]
    exact hz'
  obtain ⟨S, hSY, hS2, hAS, hSQ⟩ := exists_invariant_two_subgroup hp hp2 (Y := (H ⊔ O) ⊓ (T ⊔ (M ⊔ O)))
    (Q := ((H ⊔ O) ⊓ (T ⊔ (M ⊔ O))) ⊓ (M ⊔ O)) (O := O) (A := A)
    (le_inf hOY (le_sup_right)) inf_le_left hYO hYQ hOp hcomm h2 hAp hAY hAO hnQ
  refine ⟨S, ?_, hS2, hAS, fun hSO => hSQ (le_inf hSY (hSO.trans le_sup_right))⟩
  rw [hH]
  exact hSY.trans inf_le_left

end CFSG.LocalAnalysis.GLTheoremA
