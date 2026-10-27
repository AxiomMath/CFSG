module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FStar2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chains
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Standard
import CFSG.GroupTheory.OddOverlap

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78
open scoped Pointwise

variable {G : Type} [Group G]

theorem layerIn_le_normalizer [Finite G] {M X : Subgroup G} (h : IsCompIn M X) :
    layerIn X ≤ normalizer (M : Set G) := by
  refine sSup_le fun K hK => ?_
  by_cases hKM : K = M
  · rw [hKM]
    exact Subgroup.le_normalizer
  · intro x hx
    refine Subgroup.centralizer_le_normalizer (M : Set G) (mem_centralizer_iff.2 fun b hb => ?_)
    exact ((hK : IsCompIn K X).commute_of_ne h hKM x hx b hb).symm

theorem conjClosure_of_le_normalizer {L S : Subgroup G} (h : S ≤ normalizer (L : Set G)) :
    conjClosure L S = L := by
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    exact (mem_normalizer_iff_map_conj_eq.1 (h hg)).le
  · refine le_iSup₂_of_le 1 S.one_mem ?_
    intro x hx
    exact ⟨x, hx, by simp⟩

theorem isPGroup_sup_zpowers [Finite G] {T : Subgroup G} {s : G} (hT : IsPGroup 2 T)
    (hN : s ∈ normalizer (T : Set G)) (hs2 : s ^ 2 ∈ T) : IsPGroup 2 ↥(T ⊔ zpowers s) := by
  have hsq : ∀ y ∈ T ⊔ zpowers s, y ^ 2 ∈ T := by
    intro y hy
    have hle : zpowers s ≤ normalizer (T : Set G) := by
      rw [Subgroup.zpowers_le]
      exact hN
    have hmem : y ∈ ((zpowers s : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (zpowers s) T hle]
      exact (sup_comm T (zpowers s)) ▸ hy
    obtain ⟨a, ha, t, ht, rfl⟩ := hmem
    obtain ⟨m, rfl⟩ := ha
    have hconj : ∀ z ∈ T, s * z * s⁻¹ ∈ T := fun z hz =>
      (Subgroup.mem_normalizer_iff.1 hN z).1 hz
    have hconj' : ∀ z ∈ T, s⁻¹ * z * s ∈ T := fun z hz => by
      have := (Subgroup.mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem hN) z).1 hz
      simpa using this
    have hs2' : ∀ q : ℤ, s ^ (2 * q) ∈ T := fun q => by
      have : s ^ (2 * q) = (s ^ 2) ^ q := by rw [zpow_mul]; norm_cast
      rw [this]
      exact zpow_mem hs2 q
    obtain ⟨q, r, hr, hm⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ m = 2 * q + r :=
      ⟨m / 2, m % 2, by omega, by omega⟩
    rw [hm]
    rcases hr with rfl | rfl
    · have h0 : s ^ (2 * q + 0) * t ∈ T := mul_mem (by simpa using hs2' q) ht
      have : (s ^ (2 * q + 0) * t) ^ 2 ∈ T := pow_mem h0 2
      simpa using this
    · have e1 : s ^ (2 * q + 1) * t = (s ^ (2 * q)) * (s * t * s⁻¹) * s := by
        rw [zpow_add_one]; group
      have hy : s ^ (2 * q + 1) * t = ((s ^ (2 * q)) * (s * t * s⁻¹)) * s := by
        rw [e1]
      have hu : (s ^ (2 * q)) * (s * t * s⁻¹) ∈ T := mul_mem (hs2' q) (hconj t ht)
      set u := (s ^ (2 * q)) * (s * t * s⁻¹) with hudef
      have : (s ^ (2 * q + 1) * t) ^ 2 = u * (s * u * s⁻¹) * s ^ 2 := by
        rw [hy, pow_two]; group
      rw [this]
      exact mul_mem (mul_mem hu (hconj u hu)) hs2
  intro y
  obtain ⟨k, hk⟩ := hT ⟨y ^ 2, hsq y y.2⟩
  refine ⟨k + 1, ?_⟩
  apply Subtype.ext
  have := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
  calc (y : G) ^ 2 ^ (k + 1) = ((y : G) ^ 2) ^ 2 ^ k := by rw [pow_succ', pow_mul]
    _ = 1 := this


theorem mem_normalizer_of_stdBare [Finite G] {L T : Subgroup G} (hL : StdBare L)
    (hTL : T ≤ centralizer (L : Set G)) (hev : 2 ∣ Nat.card T) {y : G}
    (hy : ∀ x ∈ T, x * y = y * x) : y ∈ normalizer (L : Set G) :=
  StandardSubgroupAPI.mem_of_odd_inf_map_conj hL.2 hTL hev hy

theorem eq_of_le_of_iso [Finite G] {L L' : Subgroup G} (hle : L ≤ L')
    (hLq : CFSG.IsQuasisimple ↥L) (hL'q : CFSG.IsQuasisimple ↥L')
    (hiso : Nonempty ((↥L ⧸ center ↥L) ≃* (↥L' ⧸ center ↥L'))) : L = L' := by
  obtain ⟨e⟩ := hiso
  let φ : ↥L →* ↥L' ⧸ center ↥L' :=
    (QuotientGroup.mk' (center ↥L')).comp (Subgroup.inclusion hle)
  have hker : φ.ker ≤ center ↥L := by
    intro x hx
    have hxc : (Subgroup.inclusion hle x : ↥L') ∈ center ↥L' := by
      simpa [φ, QuotientGroup.eq_one_iff] using hx
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.1 hxc (Subgroup.inclusion hle g)
    exact Subtype.ext (by simpa using congrArg (fun z : ↥L' => (z : G)) this)
  have hkerle : Nat.card φ.ker ≤ Nat.card (center ↥L) := Subgroup.card_le_of_le hker
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card ↥L := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card (↥L ⧸ center ↥L) * Nat.card (center ↥L) = Nat.card ↥L :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)).symm
  have h3 : Nat.card (↥L ⧸ center ↥L) = Nat.card (↥L' ⧸ center ↥L') := Nat.card_congr e.toEquiv
  have hpos : 0 < Nat.card (center ↥L) := Nat.card_pos
  have hrange : Nat.card (↥L' ⧸ center ↥L') ≤ Nat.card φ.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.ker * Nat.card φ.range < Nat.card (center ↥L) *
        Nat.card (↥L ⧸ center ↥L) := by
      calc Nat.card φ.ker * Nat.card φ.range ≤ Nat.card (center ↥L) * Nat.card φ.range :=
            Nat.mul_le_mul_right _ hkerle
        _ < Nat.card (center ↥L) * Nat.card (↥L ⧸ center ↥L) :=
            Nat.mul_lt_mul_of_pos_left (h3 ▸ hlt) hpos
    have h2' : Nat.card (center ↥L) * Nat.card (↥L ⧸ center ↥L) = Nat.card ↥L := by
      rw [mul_comm]
      exact h2
    omega
  have hrt : φ.range = ⊤ := Subgroup.eq_top_of_le_card _ hrange
  have hx : ∀ x : ↥L', ∃ a : ↥L, ∃ z ∈ center ↥L', x = Subgroup.inclusion hle a * z := by
    intro x
    have hmem : QuotientGroup.mk x ∈ φ.range := hrt ▸ Subgroup.mem_top _
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, (Subgroup.inclusion hle a)⁻¹ * x, QuotientGroup.eq.1 ha, by group⟩
  have hAn : (L.subgroupOf L').Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, z, hz, rfl⟩ := hx g
    have hzn : z * n * z⁻¹ = n := by
      calc z * n * z⁻¹ = (n * z) * z⁻¹ := by rw [(Subgroup.mem_center_iff.1 hz n).symm]
        _ = n := by group
    have ha' : Subgroup.inclusion hle a ∈ L.subgroupOf L' := a.2
    have hconj : Subgroup.inclusion hle a * z * n * (Subgroup.inclusion hle a * z)⁻¹ =
        Subgroup.inclusion hle a * n * (Subgroup.inclusion hle a)⁻¹ := by
      calc Subgroup.inclusion hle a * z * n * (Subgroup.inclusion hle a * z)⁻¹
          = Subgroup.inclusion hle a * (z * n * z⁻¹) * (Subgroup.inclusion hle a)⁻¹ := by group
        _ = _ := by rw [hzn]
    rw [hconj]
    exact (L.subgroupOf L').mul_mem ((L.subgroupOf L').mul_mem ha' hn)
      ((L.subgroupOf L').inv_mem ha')
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hL'q hAn with htop | hcent
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.1 htop)
  · exfalso
    refine not_forall_commute_of_isQuasisimple hLq fun a ha b hb => ?_
    have h1 : (⟨a, hle ha⟩ : ↥L') ∈ L.subgroupOf L' := ha
    have := Subgroup.mem_center_iff.1 (hcent h1) ⟨b, hle hb⟩
    exact congrArg Subtype.val this.symm


theorem link5a_false_of_stdBare [Finite G] {Li Lp T : Subgroup G} {s : G}
    (hLi : IsCompIn Li (centralizer (T : Set G))) (hs : s ∈ normalizer (T : Set G))
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hincl : Lp ≤ Li ⊔ Li.map (MulAut.conj s).toMonoidHom)
    (heq : Li ⊔ Li.map (MulAut.conj s).toMonoidHom =
      conjClosure Lp (layerIn (centralizer (T : Set G))))
    (hne : Lp ≠ Li) (hLpq : CFSG.IsQuasisimple ↥Lp) (hstd : StdBare Lp)
    (h5a : Li ≠ Li.map (MulAut.conj s).toMonoidHom) : False := by
  set X : Subgroup G := centralizer (T : Set G) with hX
  set A' : Subgroup G := Li.map (MulAut.conj s).toMonoidHom with hA'def
  have hA' : IsCompIn A' X :=
    isCompIn_map_conj_of_mem_normalizer hLi (mem_normalizer_centralizer_of_mem_normalizer hs)
  have hcomm : ∀ a ∈ Li, ∀ b ∈ A', a * b = b * a := hLi.commute_of_ne hA' h5a
  have hPX : Li ⊔ A' ≤ X := sup_le hLi.1 hA'.1
  have hTLp : T ≤ centralizer (Lp : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun l hl => (mem_centralizer_iff.1 (hPX (hincl hl)) x hx).symm
  have hev : 2 ∣ Nat.card T := two_dvd_card_of_isPGroup hT2 hT
  have hgen : ∀ B : Subgroup G, B ≤ X → B ≤ normalizer (Lp : Set G) := fun B hB y hy =>
    mem_normalizer_of_stdBare hstd hTLp hev (mem_centralizer_iff.1 (hB hy))
  have hPN : Li ⊔ A' ≤ normalizer (Lp : Set G) := sup_le (hgen Li hLi.1) (hgen A' hA'.1)
  have hLpn : (Lp.subgroupOf (Li ⊔ A')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hincl).2 hPN
  have hPNLi : Li ⊔ A' ≤ normalizer (Li : Set G) :=
    sup_le Subgroup.le_normalizer (fun b hb => Subgroup.centralizer_le_normalizer (Li : Set G)
      (mem_centralizer_iff.2 fun a ha => hcomm a ha b hb))
  have hPNA' : Li ⊔ A' ≤ normalizer (A' : Set G) :=
    sup_le (fun a ha => Subgroup.centralizer_le_normalizer (A' : Set G)
      (mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)) Subgroup.le_normalizer
  have hLiP : IsCompIn Li (Li ⊔ A') :=
    isCompIn_of_normal le_sup_left hLi.isQuasisimple
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hPNLi)
  have hA'P : IsCompIn A' (Li ⊔ A') :=
    isCompIn_of_normal le_sup_right hA'.isQuasisimple
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hPNA')
  let Q : Bool → Subgroup G := fun b => bif b then Li else A'
  have hPQ : Li ⊔ A' = ⨆ b, Q b := by
    rw [iSup_bool_eq]
    rfl
  have hQ : ∀ b, IsCompIn (Q b) (Li ⊔ A') := fun b => by cases b <;> assumption
  obtain ⟨b, hb⟩ := exists_eq_of_normal hPQ hQ hincl hLpn hLpq
  cases b
  ·
    have hLpA' : Lp = A' := hb
    rw [hLpA', conjClosure_of_le_normalizer (layerIn_le_normalizer hA')] at heq
    have hLiA' : Li ≤ A' := le_sup_left.trans heq.le
    exact not_forall_commute_of_isQuasisimple hLi.isQuasisimple fun a ha b hb' =>
      hcomm a ha b (hLiA' hb')
  · exact hne hb

section Chain

variable {N : Subgroup G} {n : ℕ} {L T : ℕ → Subgroup G} {s : ℕ → G}

theorem Sol78Chain23.lt [Finite G] (h : Sol78Chain23 G N n L T s) {i : ℕ} (hi : 1 ≤ i)
    (hin : i ≤ n) (hT : T i ≠ ⊥) : Lt (L (i - 1)) (L i) := by
  obtain ⟨hTp, hLc⟩ := h.comp i hin
  obtain ⟨hsp, hsN, hs2, hLp⟩ := h.elem i hi hin
  obtain ⟨hincl, -⟩ := h.incl i hi hin
  have hSN : T i ⊔ zpowers (s i) ≤ normalizer (T i : Set G) :=
    sup_le Subgroup.le_normalizer (by rw [Subgroup.zpowers_le]; exact hsN)
  refine ⟨T i ⊔ zpowers (s i), T i, fun hbot => hT (le_bot_iff.1 (hbot ▸ le_sup_left)), hT,
    isPGroup_sup_zpowers hTp hsN hs2, hTp, ?_, hLp, hLc, ?_⟩
  · refine Subgroup.commutator_le.2 fun x hx y hy => ⟨?_, ?_⟩
    · have hy' : y ∈ T i ⊔ zpowers (s i) := (le_sup_left : T i ≤ T i ⊔ zpowers (s i)) hy
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy')
        (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy')
    · have h1 : x * y * x⁻¹ ∈ T i := (Subgroup.mem_normalizer_iff.1 (hSN hx) y).1 hy
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy)
  · refine hincl.trans (sup_le ?_ ?_)
    · exact le_iSup₂_of_le 1 (one_mem _) fun x hx => ⟨x, hx, by simp⟩
    · exact le_iSup₂_of_le (s i) (mem_sup_right (mem_zpowers _)) le_rfl

theorem FStarSimple.eq_of_isCompIn_bot [Finite G] (hN : FStarSimple N) {M : Subgroup G}
    (hM : IsCompIn M (centralizer (((⊥ : Subgroup G)) : Set G))) : M = N := by
  have htop : centralizer (((⊥ : Subgroup G)) : Set G) = ⊤ := by
    ext x
    simp only [mem_top, iff_true]
    rw [mem_centralizer_iff]
    intro g hg
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hg
    rw [hg, one_mul, mul_one]
  have hsub : M.IsSubnormal := by
    have h1 : (M.subgroupOf (centralizer (((⊥ : Subgroup G)) : Set G))).IsSubnormal := hM.2.2
    rw [htop] at h1
    have h2 := h1.map (f := (Subgroup.topEquiv (G := G)).toMonoidHom)
      (Subgroup.topEquiv (G := G)).surjective
    have h3 : (M.subgroupOf (⊤ : Subgroup G)).map
        (Subgroup.topEquiv (G := G)).toMonoidHom = M := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, trivial⟩, hx, rfl⟩⟩
    rwa [h3] at h2
  exact hN.eq_of_isComponent hM.isQuasisimple hsub

theorem Sol78Chain23.T_ne_bot [Finite G] (hN : FStarSimple N) (h : Sol78Chain23 G N n L T s)
    {i : ℕ} (hi : i < n) : T i ≠ ⊥ := by
  intro hbot
  obtain ⟨-, hLc⟩ := h.comp i hi.le
  rw [hbot] at hLc
  have hLeqN : L i = N := hN.eq_of_isCompIn_bot hLc
  exact absurd (h.inj i hi.le n le_rfl (by rw [h.last]; exact hLeqN)) (Nat.ne_of_lt hi)

end Chain

end CFSG.EvenSporadicStandard.Induction
