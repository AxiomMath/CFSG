module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBlockSub
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBlockMod
import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltBaumMod

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
  CFSG.AGLEmbedding CFSG.RankThree.PartTwo Equiv
open scoped commutatorElement

section Main

variable {X : Type} [Group X] [Finite X] {T K Y : Subgroup X} {n : ℕ}
  {Φ : ↥K →* alternatingGroup (Fin n)} {π : ↥⁅gnV T, K⁆ →* Multiplicative (evenWeight n)}

theorem IsLiftedBlock.isShort2_and_isAltType (hX : GNSetting X T) (hY : IsLiftedBlock T K Y)
    (hn : 9 ≤ n) (hodd : Odd n) (hCK : gnC T ≤ K) (hΦs : Function.Surjective Φ)
    (hΦk : ∀ k : ↥K, Φ k = 1 ↔ (k : X) ∈ gnC T) (hS : AltBaumSetup (gnV T) K Φ)
    (hπ : AltBaumSection (gnV T) K Φ π) : IsShort2 Y ∧ IsAltType Y n := by
  have h5 : 5 ≤ n := by omega
  have hU : blockU Y = ⁅gnV T, Y⁆ := hY.blockU_eq hX h5 hΦs hΦk hCK
  have hUle : blockU Y ≤ ⁅gnV T, K⁆ := hU ▸ Subgroup.commutator_mono le_rfl hY.le
  have hUV : ⁅gnV T, K⁆ ≤ gnV T := commutator_le_of_invariant (gnV T) K hS.norm
  have hinj := hπ.injective hS hodd hn
  have hα : Function.Surjective (liftAlpha hY.le Φ) := hY.liftAlpha_surjective h5 hΦs hΦk
  have hR : pCoreOf 2 Y = Y ⊓ gnC T := hY.pCoreOf_eq hX h5 hΦs hΦk
  have hUR : blockU Y ≤ pCoreOf 2 Y :=
    Subgroup.le_normalizer_iff_commutator_le_left.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  let β : ↥(blockU Y) →* Multiplicative (evenWeight n) := π.comp (Subgroup.inclusion hUle)
  have hβinj : Function.Injective β := hinj.comp (Subgroup.inclusion_injective hUle)
  have hUN : ∀ y ∈ Y, ∀ u ∈ blockU Y, y * u * y⁻¹ ∈ blockU Y := fun y hy u hu =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.normalizer_commutator_ge_right _ _ hy) u).1 hu
  have hβe : ∀ (ℓ : ↥Y) (u v : ↥(blockU Y)), (v : X) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) = evenWeightPerm (liftAlpha hY.le Φ ℓ : Perm (Fin n))
        (Multiplicative.toAdd (β u)) := fun ℓ u v h =>
    hπ.equivar ⟨ℓ, hY.le ℓ.2⟩ (Subgroup.inclusion hUle u) (Subgroup.inclusion hUle v) h
  have hne : blockU Y ≠ ⊥ := by
    rw [hU]
    intro h
    apply hY.not_le_gnC
    have : gnV T ≤ Subgroup.centralizer (Y : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    exact Subgroup.le_centralizer_iff.1 this
  obtain ⟨hβs, hirr, hfix⟩ :=
    natural_block_facts hodd (by omega) (liftAlpha hY.le Φ) hα β hβinj hUN hβe hne
  have hZ : blockZ Y = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzU, hzC⟩
    rw [Subgroup.mem_bot]
    refine hfix z hzU fun y hy => ?_
    have := Subgroup.mem_centralizer_iff.1 hzC y hy
    rw [this]; group
  have hKer : (liftAlpha hY.le Φ).ker = CFSG.pCore 2 ↥Y := by
    apply Subgroup.map_injective Y.subtype_injective
    have hpc : (CFSG.pCore 2 ↥Y).map Y.subtype = Y ⊓ gnC T := hR
    rw [hpc]
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hΦk ⟨y, hY.le y.2⟩).1 hy⟩
    · rintro ⟨hxY, hxC⟩
      exact ⟨⟨x, hxY⟩, (hΦk ⟨x, hY.le hxY⟩).2 hxC, rfl⟩
  have h1 : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → N = ⊤ := by
    intro N _ hN
    have hodd' : ∀ x : ↥Y, Odd (orderOf x) → x ∈ N := by
      intro x hx
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hN (QuotientGroup.mk x)
      have hd : orderOf (QuotientGroup.mk x : ↥Y ⧸ N) ∣ orderOf x :=
        orderOf_map_dvd (QuotientGroup.mk' N) x
      have hk0 : k = 0 := by
        by_contra hk0
        have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
        rw [← hk] at h2
        exact (Nat.not_even_iff_odd.2 hx) (even_iff_two_dvd.2 (h2.trans hd))
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      exact (QuotientGroup.eq_one_iff x).1 hk
    have hcl : Subgroup.closure {x : ↥Y | Odd (orderOf x)} ≤ N :=
      (Subgroup.closure_le N).2 hodd'
    rw [eq_top_iff]
    intro x _
    have hx : (x : X) ∈ Subgroup.closure {y : X | y ∈ Y ∧ Odd (orderOf y)} := hY.odd x.2
    have hxm : (x : X) ∈ (Subgroup.closure {x : ↥Y | Odd (orderOf x)}).map Y.subtype := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_ hx
      rintro y ⟨hyY, hyo⟩
      exact ⟨⟨y, hyY⟩, by simpa [Subgroup.orderOf_coe] using hyo, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hxm
    have : z = x := Subtype.ext hzx
    rw [← this]; exact hcl hz
  have h2 : CharTwo Y := by
    intro y hy
    obtain ⟨hyY, hyc⟩ := hy
    have hyU : ∀ u ∈ blockU Y, y * u * y⁻¹ = u := by
      intro u hu
      have := Subgroup.mem_centralizer_iff.1 hyc u (hUR hu)
      rw [mul_inv_eq_iff_eq_mul]; exact this.symm
    have hσ : ∀ v : evenWeight n,
        evenWeightPerm (liftAlpha hY.le Φ ⟨y, hyY⟩ : Perm (Fin n)) v = v := by
      intro v
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
      have h := hβe ⟨y, hyY⟩ u u (hyU u u.2).symm
      rw [hu] at h
      exact h.symm
    have hα1 : liftAlpha hY.le Φ ⟨y, hyY⟩ = 1 :=
      Subtype.ext (eq_one_of_evenWeightPerm_eq_self hodd hσ)
    have : (y : X) ∈ gnC T := (hΦk ⟨y, hY.le hyY⟩).1 hα1
    rw [hR]; exact ⟨hyY, this⟩
  have h3 : blockU Y ≤ blockQ Y ⊓ Subgroup.centralizer (blockQ Y : Set X) := by
    refine le_inf hUR fun u hu => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrC : r ∈ gnC T := (hR ▸ hr : r ∈ Y ⊓ gnC T).2
    have huV : u ∈ gnV T := hUV (hUle hu)
    exact ((Subgroup.mem_centralizer_iff.1 hrC) u huV).symm
  have h3' : ∀ x ∈ blockU Y, x ^ 2 = 1 := fun x hx => by
    rw [pow_two]; exact hS.sq x (hUV (hUle hx))
  have hquot : (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hKer.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hα)
  have h4 : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    B1Red.isQuasisimple_of_open (isQuasisimple_of_alt h5 hquot)
  have h5' : blockZ Y < blockU Y ∧ ∀ W : Subgroup X, blockZ Y ≤ W → W ≤ blockU Y →
      Y ≤ Subgroup.normalizer (W : Set X) → W = blockZ Y ∨ W = blockU Y := by
    refine ⟨by rw [hZ]; exact bot_lt_iff_ne_bot.2 hne, fun W _ hWU hWN => ?_⟩
    have hWN' : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W := fun y hy w hw =>
      (Subgroup.mem_normalizer_iff.1 (hWN hy) w).1 hw
    rcases hirr W hWU hWN' with h | h
    · left; rw [hZ]; exact h
    · right; exact h
  refine ⟨⟨h1, h2, ⟨h3, h3'⟩, Or.inl h4, h5'⟩, liftAlpha hY.le Φ, hα, hKer, β, hβs, ?_, ?_⟩
  · ext u
    rw [MonoidHom.mem_ker, hZ, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro h; exact congrArg Subtype.val (hβinj (h.trans (map_one β).symm))
    · intro h
      have : u = 1 := Subtype.ext h
      rw [this, map_one]
  · intro ℓ u v h i
    have := hβe ℓ u v h
    show ((Multiplicative.toAdd (β v) : evenWeight n) : Fin n → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : evenWeight n) : Fin n → ZMod 2)
        ((liftAlpha hY.le Φ ℓ : Perm (Fin n))⁻¹ i)
    rw [this]; rfl

theorem IsLiftedBlock.inClassXBlock (hX : GNSetting X T) (hY : IsLiftedBlock T K Y)
    (hn : 9 ≤ n) (hodd : Odd n) (hCK : gnC T ≤ K) (hΦs : Function.Surjective Φ)
    (hΦk : ∀ k : ↥K, Φ k = 1 ↔ (k : X) ∈ gnC T) (hS : AltBaumSetup (gnV T) K Φ)
    (hπ : AltBaumSection (gnV T) K Φ π) : InClassXBlock Y := by
  obtain ⟨hshort, halt⟩ := hY.isShort2_and_isAltType hX hn hodd hCK hΦs hΦk hS hπ
  obtain ⟨m, hm⟩ := hodd
  exact ⟨hshort, Or.inr ⟨m, by omega, by rw [← hm]; exact halt⟩⟩

end Main

section Contradiction

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem false_of_block_of_altBaumSection (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) {n : ℕ} (hn : 9 ≤ n) (hodd : Odd n)
    {Φ : ↥(L.comap (QuotientGroup.mk' (gnC T))) →* alternatingGroup (Fin n)}
    (hΦs : Function.Surjective Φ) (hΦk : ∀ k, Φ k = 1 ↔ (k : X) ∈ gnC T)
    {π : ↥⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (evenWeight n)}
    (hS : AltBaumSetup (gnV T) (L.comap (QuotientGroup.mk' (gnC T))) Φ)
    (hπ : AltBaumSection (gnV T) (L.comap (QuotientGroup.mk' (gnC T))) Φ π)
    {H Kb : Subgroup X} (hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ H) (hblk : IsBlock2 H Kb)
    (hC : ¬ Kb ≤ gnC T) (hKL : gnImg T Kb ≤ L) : False := by
  set K : Subgroup X := L.comap (QuotientGroup.mk' (gnC T)) with hK
  have hKb : Kb ≤ K := fun x hx => hKL (Subgroup.mem_map_of_mem _ hx)
  have hCK : gnC T ≤ K := fun c hc => by
    show QuotientGroup.mk' (gnC T) c ∈ L
    rw [show QuotientGroup.mk' (gnC T) c = 1 from (QuotientGroup.eq_one_iff c).2 hc]
    exact L.one_mem
  have hY := isLiftedBlock_liftBlock hX hKb hQH hblk hC
  have hXB := hY.inClassXBlock hX hn hodd hCK hΦs hΦk hS hπ
  have hKsub : IsSubnormal K ⊤ := by
    have h1 := CFSG.Open.IsSubnormal.comap (QuotientGroup.mk' (gnC T)) hL.2.1
    rwa [Subgroup.comap_top] at h1
  exact hX.noXBlock _ (IsSubnormal.step hY.le hY.normal_subgroupOf hKsub) hXB

end Contradiction

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
