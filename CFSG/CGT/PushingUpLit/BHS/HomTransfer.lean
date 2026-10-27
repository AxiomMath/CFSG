module

public import CFSG.CGT.PushingUpLit.BHS.MinParabolic
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

structure MinPar (P T M : Subgroup G) : Prop where
  syl : IsSylowOf 2 T P
  not_normal : ¬ P ≤ Subgroup.normalizer (T : Set G)
  le_M : T ≤ M
  lt_P : M < P
  max : ∀ X : Subgroup G, T ≤ X → X < P → X ≤ M

namespace MinPar

variable {P T M : Subgroup G} (h : MinPar P T M)

include h

theorem T_le : T ≤ P := h.syl.1

theorem M_le : M ≤ P := h.lt_P.le

theorem maximal {X : Subgroup G} (hMX : M ≤ X) (hXP : X ≤ P) : X = M ∨ X = P := by
  by_cases hXP' : X = P
  · exact Or.inr hXP'
  · left
    exact le_antisymm (h.max X (h.le_M.trans hMX) (lt_of_le_of_ne hXP hXP')) hMX

theorem sup_eq_of_not_le {N : Subgroup G} (hNP : N ≤ P) (hNM : ¬ N ≤ M) : N ⊔ T = P := by
  refine le_antisymm (sup_le hNP h.T_le) ?_
  by_contra hlt
  have hlt' : N ⊔ T < P := lt_of_le_of_ne (sup_le hNP h.T_le) fun h' => hlt h'.ge
  exact hNM (le_sup_left.trans (h.max _ le_sup_right hlt'))

end MinPar

section Tools

theorem relIndex_eq_two_pow [Finite G] {K D : Subgroup G}
    (hDn : K ≤ Subgroup.normalizer (D : Set G)) (h2 : ∀ k ∈ K, ∃ n : ℕ, k ^ 2 ^ n ∈ D) :
    ∃ m : ℕ, D.relIndex K = 2 ^ m := by
  have : (D.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDn
  have hp : IsPGroup 2 (↥K ⧸ D.subgroupOf K) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨n, hn⟩ := h2 k k.2
      refine ⟨n, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 (by simpa using hn)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hp
  exact ⟨m, by simpa [Subgroup.relIndex, Subgroup.index] using hm⟩

theorem le_inf_sup_of_two_pow_mem [Finite G] {P T K D : Subgroup G} (hT : IsSylowOf 2 T P)
    (hKP : K ≤ P) (hKn : P ≤ Subgroup.normalizer (K : Set G))
    (hDn : P ≤ Subgroup.normalizer (D : Set G)) (h2 : ∀ k ∈ K, ∃ n : ℕ, k ^ 2 ^ n ∈ D) :
    K ≤ (K ⊓ T) ⊔ D := by
  set N' := (K ⊓ T) ⊔ D with hN'
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 T P := CFSG.ABGLocalTools.isSylowOf_iff.mpr hT
  have hS' := hS.inf_of_le_normalizer hKP hKn
  have hodd : ¬ 2 ∣ (T ⊓ K).relIndex K := (CFSG.ABGLocalTools.isSylowOf_iff.1 hS').2.2
  have hd1 : N'.relIndex K ∣ (T ⊓ K).relIndex K := by
    rw [inf_comm]
    exact Subgroup.relIndex_dvd_of_le_left K le_sup_left
  have hd2 : N'.relIndex K ∣ D.relIndex K := Subgroup.relIndex_dvd_of_le_left K le_sup_right
  obtain ⟨m, hm⟩ := relIndex_eq_two_pow (hKP.trans hDn) h2
  obtain ⟨j, hj, hjN⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hm ▸ hd2)
  have hj0 : j = 0 := by
    by_contra hne
    exact hodd (dvd_trans (hjN ▸ dvd_pow_self 2 hne) hd1)
  have h1 : N'.relIndex K = 1 := by rw [hjN, hj0, pow_zero]
  exact Subgroup.relIndex_eq_one.1 h1

variable {H : Type*} [Group H]

theorem map_maximal (f : G →* H) {M P : Subgroup G} (hMP : M < P)
    (hmax : ∀ X : Subgroup G, M ≤ X → X ≤ P → X = M ∨ X = P) (hker : f.ker ⊓ P ≤ M) :
    M.map f < P.map f ∧
      ∀ Y : Subgroup H, M.map f ≤ Y → Y ≤ P.map f → Y = M.map f ∨ Y = P.map f := by
  refine ⟨lt_of_le_of_ne (Subgroup.map_mono hMP.le) fun heq => hMP.not_ge ?_, ?_⟩
  · intro p hp
    have : f p ∈ M.map f := heq ▸ Subgroup.mem_map_of_mem f hp
    obtain ⟨m, hm, hmp⟩ := this
    have h1 : m⁻¹ * p ∈ f.ker ⊓ P := ⟨by simp [hmp], P.mul_mem (P.inv_mem (hMP.le hm)) hp⟩
    have := M.mul_mem hm (hker h1)
    simpa using this
  · intro Y hMY hYP
    set X : Subgroup G := P ⊓ Y.comap f with hX
    have hMX : M ≤ X := le_inf hMP.le fun m hm => hMY (Subgroup.mem_map_of_mem f hm)
    rcases hmax X hMX inf_le_left with hXM | hXP
    · left
      refine le_antisymm (fun y hy => ?_) hMY
      obtain ⟨p, hp, rfl⟩ := hYP hy
      have : p ∈ X := ⟨hp, hy⟩
      rw [hXM] at this
      exact Subgroup.mem_map_of_mem f this
    · right
      refine le_antisymm hYP ?_
      rintro _ ⟨p, hp, rfl⟩
      have : p ∈ X := by rw [hXP]; exact hp
      exact this.2

theorem isSylowOf_map [Finite G] [Finite H] (f : G →* H) {T P : Subgroup G} (h : IsSylowOf 2 T P) :
    IsSylowOf 2 (T.map f) (P.map f) := by
  have hA : CFSG.ABGLocalTools.IsSylowOf 2 T P := CFSG.ABGLocalTools.isSylowOf_iff.mpr h
  obtain ⟨Q, hQ⟩ := hA
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 (T.map f) (P.map f) := by
    refine ⟨Q.mapSurjective (f.subgroupMap_surjective P), ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, ← hQ, Subgroup.map_map]
    rfl
  exact CFSG.ABGLocalTools.isSylowOf_iff.1 h1

theorem pCoreOf_map_le [Finite G] [Finite H] (f : G →* H) {T P : Subgroup G}
    (h : IsSylowOf 2 T P) : pCoreOf 2 (P.map f) ≤ T.map f := by
  have hS : IsSylowIn 2 (T.map f) (P.map f) := isSylowOf_map f h
  refine hS.le_of_normal (pCoreOf_le 2 _) ?_ (pCoreOf_isPGroup 2 _)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).2
    (le_normalizer_pCoreOf 2 _)

theorem normalizer_ker_inf (f : G →* H) (P : Subgroup G) :
    P ≤ Subgroup.normalizer ((f.ker ⊓ P : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, P.mul_mem (P.mul_mem hg hx2) (P.inv_mem hg)⟩
    have h1 : f x = 1 := hx1
    show f (g * x * g⁻¹) = 1
    simp [h1]
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · have h1 : f (g * x * g⁻¹) = 1 := hx1
      have h2 : f x = 1 := by simpa using h1
      exact h2
    · have := P.mul_mem (P.mul_mem (P.inv_mem hg) hx2) hg
      simpa [mul_assoc] using this

theorem ker_inf_le_of_minPar [Finite G] {P T M D : Subgroup G} (f : G →* H) (h : MinPar P T M)
    (hDn : P ≤ Subgroup.normalizer (D : Set G))
    (h2 : ∀ g ∈ P, f g = 1 → ∃ n : ℕ, g ^ 2 ^ n ∈ D) (hnot : ¬ P ≤ T ⊔ D)
    (hO2 : pCoreOf 2 P ≤ D) : f.ker ⊓ P ≤ D ∧ f.ker ⊓ P ≤ M := by
  set N : Subgroup G := f.ker ⊓ P with hN
  have hNP : N ≤ P := inf_le_right
  have hNn : P ≤ Subgroup.normalizer (N : Set G) := normalizer_ker_inf f P
  have h2' : ∀ k ∈ N, ∃ n : ℕ, k ^ 2 ^ n ∈ D := fun k hk => h2 k hk.2 hk.1
  have hNle : N ≤ (N ⊓ T) ⊔ D := le_inf_sup_of_two_pow_mem h.syl hNP hNn hDn h2'
  have hNM : N ≤ M := by
    by_contra hNM
    have hsup := h.sup_eq_of_not_le hNP hNM
    apply hnot
    rw [← hsup]
    exact sup_le (hNle.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)) le_sup_left
  have hnorm := three_three_a h.syl h.lt_P h.max hNP hNn hNM
  have hNT : N ⊓ T ≤ pCoreOf 2 P :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_right.trans h.T_le) hnorm
      (h.syl.2.1.to_le inf_le_right)
  exact ⟨hNle.trans (sup_le (hNT.trans hO2) le_rfl), hNM⟩

theorem pCoreOf_map_eq_bot [Finite G] [Finite H] {P T M D : Subgroup G} (f : G →* H)
    (h : MinPar P T M) (hDP : D ≤ P) (hDn : P ≤ Subgroup.normalizer (D : Set G))
    (hDker : D ≤ f.ker) (hN : f.ker ⊓ P ≤ D) (hnot : ¬ P ≤ T ⊔ D) (hO2 : pCoreOf 2 P ≤ D) :
    pCoreOf 2 (P.map f) = ⊥ := by
  set R : Subgroup H := pCoreOf 2 (P.map f) with hR
  refine eq_bot_iff.2 fun r hr => ?_
  obtain ⟨t, htT, rfl⟩ := pCoreOf_map_le f h.syl hr
  rw [Subgroup.mem_bot]
  set C : Subgroup G := P ⊓ R.comap f with hC
  have hCP : C ≤ P := inf_le_left
  have hRn : P.map f ≤ Subgroup.normalizer (R : Set H) := le_normalizer_pCoreOf 2 _
  have hCn : P ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have hfg := Subgroup.mem_normalizer_iff.1 (hRn (Subgroup.mem_map_of_mem f hg))
    intro x
    simp only [hC, Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨P.mul_mem (P.mul_mem hg hx1) (P.inv_mem hg), (hfg _).1 hx2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, (hfg _).2 hx2⟩
      have := P.mul_mem (P.mul_mem (P.inv_mem hg) hx1) hg
      simpa [mul_assoc] using this
  have hDC : D ≤ C := fun d hd => ⟨hDP hd, by
    simp [MonoidHom.mem_ker.1 (hDker hd)]⟩
  have h2C : ∀ c ∈ C, ∃ n : ℕ, c ^ 2 ^ n ∈ D := by
    intro c hc
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (P.map f)) ⟨f c, hc.2⟩
    refine ⟨k, hN ⟨?_, P.pow_mem hc.1 _⟩⟩
    have := congrArg Subtype.val hk
    simpa [MonoidHom.mem_ker] using this
  have hCle : C ≤ (C ⊓ T) ⊔ D := le_inf_sup_of_two_pow_mem h.syl hCP hCn hDn h2C
  have hCM : C ≤ M := by
    by_contra hCM
    have hsup := h.sup_eq_of_not_le hCP hCM
    apply hnot
    rw [← hsup]
    exact sup_le (hCle.trans (sup_le (inf_le_right.trans le_sup_left) le_sup_right)) le_sup_left
  have hnorm := three_three_a h.syl h.lt_P h.max hCP hCn hCM
  have hCT : C ⊓ T ≤ pCoreOf 2 P :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_right.trans h.T_le) hnorm
      (h.syl.2.1.to_le inf_le_right)
  have htC : t ∈ C := ⟨h.T_le htT, by simpa [Subgroup.mem_comap] using hr⟩
  exact MonoidHom.mem_ker.1 (hDker (hO2 (hCT ⟨htC, htT⟩)))

end Tools

end CFSG.CGT.PushingUpLit.BHS
