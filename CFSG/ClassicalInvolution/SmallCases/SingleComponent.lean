module

public import CFSG.ClassicalInvolution.Balance.TheoremQNormalizer
public import CFSG.ClassicalInvolution.Generic.Frame
import CFSG.ClassicalInvolution.Balance.Quotient
import CFSG.ClassicalInvolution.PerfectCase.Basic
import CFSG.ClassicalInvolution.SubnormalClosure.Reduction

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section TwoComponents

variable {W : Type*} [Group W] [Finite W]

theorem eq_of_isTwoComponent_of_perfect_le {K K' L : Subgroup W}
    (hK : TwoComponents.IsTwoComponent K) (hK' : TwoComponents.IsTwoComponent K')
    (hLK : L ≤ K) (hLK' : L ≤ K') (hperf : commutator L = ⊤) (hne : L ≠ ⊥) : K = K' := by
  by_contra hne'
  obtain ⟨-, -, hcomm⟩ :=
    TwoComponentInteraction.mutual_normalization_core_commutation K K' hK hK' hne'
  have hself : ⁅L, L⁆ = L := by
    have : Group.IsPerfect L := ⟨hperf⟩
    exact Subgroup.commutator_eq_self
  have hle : L ≤ (componentClassificationOddCore K).map K.subtype :=
    calc L = ⁅L, L⁆ := hself.symm
      _ ≤ ⁅K, K'⁆ := Subgroup.commutator_mono hLK hLK'
      _ ≤ _ := hcomm.trans inf_le_left
  have hodd : Odd (Nat.card L) := by
    have h1 : Odd (Nat.card ((componentClassificationOddCore K).map K.subtype)) := by
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact OddCore.odd_card K
    exact h1.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  exact hne (eq_bot_of_perfect_of_odd hperf hodd)

theorem isTwoComponent_of_perfect {M : Subgroup W} (hM : IsSubnormal M ⊤) (hperf : commutator M = ⊤)
    (hq : CFSG.Open.IsQuasisimple (M ⧸ componentClassificationOddCore M)) :
    TwoComponents.IsTwoComponent M := by
  obtain ⟨L, hLM, hL, hmap⟩ := exists_isTwoComponent_le M hM hq
  have hres := twoResidual_le_subgroupOf_of_map_eq hLM hL.1 hM hmap
  have htop := twoResidual_eq_top_of_perfect hperf
  have hML : M ≤ L := fun x hx => by
    have : (⟨x, hx⟩ : M) ∈ L.subgroupOf M := hres (htop ▸ Subgroup.mem_top _)
    exact this
  exact le_antisymm hLM hML ▸ hL

theorem isTwoComponent_subgroupOf_of_perfect_of_le {C M : Subgroup W} (hMC : M ≤ C)
    (hsub : IsSubnormal M C) (hperf : commutator M = ⊤)
    (hq : CFSG.Open.IsQuasisimple (M ⧸ componentClassificationOddCore M)) :
    TwoComponents.IsTwoComponent (M.subgroupOf C) := by
  let e : (M.subgroupOf C) ≃* M := Subgroup.subgroupOfEquivOfLe hMC
  have hsub' : IsSubnormal (M.subgroupOf C) ⊤ :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hMC).mpr hsub
  have hperf' : commutator (M.subgroupOf C) = ⊤ := by
    have : Group.IsPerfect M := ⟨hperf⟩
    have : Group.IsPerfect (M.subgroupOf C) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hq' : CFSG.Open.IsQuasisimple
      ((M.subgroupOf C) ⧸ componentClassificationOddCore (M.subgroupOf C)) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore (M.subgroupOf C))
        (componentClassificationOddCore M) e (OddCore.equiv_invariant e)) hq
  exact isTwoComponent_of_perfect hsub' hperf' hq'

end TwoComponents

section Conj

variable {X : Type*} [Group X]

theorem map_conj_eq_of_conj_mem (S : Subgroup X) (z : X) (h : ∀ x ∈ S, z * x * z⁻¹ ∈ S)
    (h' : ∀ x ∈ S, z⁻¹ * x * z ∈ S) : S.map (MulAut.conj z).toMonoidHom = S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h y hy
  · intro hx
    exact ⟨z⁻¹ * x * z, h' x hx, by simp [mul_assoc]⟩

theorem fixedSubgroup_conj_eq_centralizer (z : X) :
    FixedCommutingProduct.fixedSubgroup (MulAut.conj z) =
      Subgroup.centralizer ({z} : Set X) := by
  ext m
  change z * m * z⁻¹ = m ↔ m ∈ Subgroup.centralizer ({z} : Set X)
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

end Conj

section Trivial

variable {W : Type*} [Group W] [Finite W]

theorem eq_bot_of_le_sup_of_commutator_le_oddCoreIn {L M T : Subgroup W} (hperf : commutator L = ⊤)
    (hLMT : L ≤ M ⊔ T) (hMN : M ≤ Subgroup.normalizer (L : Set W))
    (hTN : T ≤ Subgroup.normalizer (L : Set W)) (hM : ⁅L, M⁆ ≤ oddCoreIn L)
    (hT : ⁅L, T⁆ ≤ oddCoreIn L) : L = ⊥ := by
  set Ω : Subgroup W := oddCoreIn L with hΩ
  let Kern : Subgroup W :=
    { carrier := {x | x ∈ Subgroup.normalizer (L : Set W) ∧ ∀ l ∈ L, ⁅l, x⁆ ∈ Ω}
      one_mem' := ⟨Subgroup.one_mem _, fun l _ => by simp⟩
      mul_mem' := fun {x y} hx hy => ⟨Subgroup.mul_mem _ hx.1 hy.1, fun l hl => by
        have e : ⁅l, x * y⁆ = ⁅l, x⁆ * (x * ⁅l, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have hxΩ : x ∈ Subgroup.normalizer (Ω : Set W) :=
          mem_normalizer_oddCoreIn_of_mem_normalizer hx.1
        exact Ω.mul_mem (hx.2 l hl) ((Subgroup.mem_normalizer_iff.mp hxΩ _).mp (hy.2 l hl))⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, fun l hl => by
        have e : ⁅l, x⁻¹⁆ = x⁻¹ * ⁅l, x⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have hxΩ : x⁻¹ ∈ Subgroup.normalizer (Ω : Set W) :=
          mem_normalizer_oddCoreIn_of_mem_normalizer (Subgroup.inv_mem _ hx.1)
        exact (Subgroup.mem_normalizer_iff.mp hxΩ _).mp (Ω.inv_mem (hx.2 l hl))⟩ }
  have hMK : M ≤ Kern := fun x hx =>
    ⟨hMN hx, fun l hl => hM (Subgroup.commutator_mem_commutator hl hx)⟩
  have hTK : T ≤ Kern := fun x hx =>
    ⟨hTN hx, fun l hl => hT (Subgroup.commutator_mem_commutator hl hx)⟩
  have hLK : L ≤ Kern := hLMT.trans (sup_le hMK hTK)
  have hLΩ : L ≤ Ω := by
    have hself : ⁅L, L⁆ = L := by
      have : Group.IsPerfect L := ⟨hperf⟩
      exact Subgroup.commutator_eq_self
    rw [← hself]
    exact Subgroup.commutator_le.mpr fun l hl l' hl' => (hLK hl').2 l hl
  exact eq_bot_of_perfect_of_odd hperf
    ((odd_card_oddCoreIn L).of_dvd_nat (Subgroup.card_dvd_of_le hLΩ))

end Trivial

section Corefree

variable {X : Type*} [Group X] [Finite X]

theorem le_centralizer_of_not_le (hX : componentClassificationOddCore X = ⊥) {z : X}
    {L K : Subgroup X} (hz1 : z ≠ 1) (hzL : z ∈ L) (hLC : L ≤ Subgroup.centralizer ({z} : Set X))
    (hL : TwoComponents.IsTwoComponent (L.subgroupOf (Subgroup.centralizer ({z} : Set X))))
    (hlayer : L ≤ TwoLayer.subgroup X) (hK : TwoComponents.IsTwoComponent K) (hKL : ¬ L ≤ K) :
    L ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨hLsub, hLperf, -⟩ := twoComponent_data hLC hL
  set C : Subgroup X := Subgroup.centralizer ({z} : Set X) with hC
  set E : Subgroup X := TwoLayer.subgroup X with hE
  have : (TwoLayer.subgroup X).Characteristic := TwoLayerTransport.characteristic X
  have hEnormal : E.Normal := inferInstance
  have hKq : CFSG.Open.IsQuasisimple K := (TwoComponents.ordinary_of_corefree hX hK).2.2
  have hzE : z ∈ E := hlayer hzL
  have hEK : E ≤ Subgroup.normalizer (K : Set X) := by
    refine sSup_le fun K' hK' => ?_
    by_cases h : K' = K
    · subst h
      exact Subgroup.le_normalizer
    · exact (TwoComponentInteraction.mutual_normalization_core_commutation K K' hK hK'
        (Ne.symm h)).1
  have hcomm : ∀ K', TwoComponents.IsTwoComponent K' → K' ≠ K → ⁅K, K'⁆ = ⊥ := fun K' hK' h =>
    TwoComponentInteraction.commutes_of_quasisimple_left K K' hK hK' (Ne.symm h) hKq
  set R : Subgroup X := E ⊓ Subgroup.centralizer (K : Set X) with hR
  have hKR : ⁅K, R⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp inf_le_right
  have hcover : E ≤ K ⊔ R := by
    refine sSup_le fun K' hK' => ?_
    by_cases h : K' = K
    · subst h
      exact le_sup_left
    · refine le_sup_of_le_right (le_inf (le_sSup hK') ?_)
      exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hcomm K' hK' h))
  have hKE : K ≤ E := le_sSup hK
  have hzK : ∀ k, z * k * z⁻¹ ∈ K ↔ k ∈ K := fun k => by
    have := (Subgroup.mem_normalizer_iff.mp (hEK hzE) k)
    exact this.symm
  have hKinv : K.map (MulAut.conj z).toMonoidHom = K :=
    map_conj_eq_of_conj_mem K z (fun x hx => (hzK x).mpr hx) (fun x hx => by
      have h := (hzK (z⁻¹ * x * z)).mp (by simpa [mul_assoc] using hx)
      exact h)
  have hRconj : ∀ g ∈ E, ∀ x ∈ R, g * x * g⁻¹ ∈ R := by
    intro g hg x hx
    refine Subgroup.mem_inf.mpr ⟨hEnormal.conj_mem x (Subgroup.mem_inf.mp hx).1 g, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hEK (E.inv_mem hg)) k).mp hk
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 _ hk'
    calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * k := by group
  have hRinv : R.map (MulAut.conj z).toMonoidHom = R :=
    map_conj_eq_of_conj_mem R z (hRconj z hzE) (fun x hx => by
      simpa using hRconj z⁻¹ (E.inv_mem hzE) x hx)
  have hder := FixedCommutingProduct.derived_fixed K R hKR (MulAut.conj z) hKinv hRinv
  rw [fixedSubgroup_conj_eq_centralizer] at hder
  have hLle : L ≤ (K ⊔ R) ⊓ C := le_inf (hlayer.trans hcover) hLC
  have hLderiv : L ≤ K ⊓ C ⊔ R ⊓ C := by
    have hself : ⁅L, L⁆ = L := by
      have : Group.IsPerfect L := ⟨hLperf⟩
      exact Subgroup.commutator_eq_self
    calc L = ⁅L, L⁆ := hself.symm
      _ ≤ ⁅(K ⊔ R) ⊓ C, (K ⊔ R) ⊓ C⁆ := Subgroup.commutator_mono hLle hLle
      _ ≤ _ := hder
  have hKsub : IsSubnormal (K ⊓ C) C := by
    have := isSubnormal_inf hK.1 C
    rwa [top_inf_eq] at this
  have hRE : IsSubnormal R E := by
    refine isSubnormal_of_normal_subgroupOf inf_le_left ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hRconj e he x hx, fun hx => ?_⟩
    have h2 := hRconj e⁻¹ (E.inv_mem he) _ hx
    have e1 : e⁻¹ * (e * x * e⁻¹) * e⁻¹⁻¹ = x := by group
    rw [e1] at h2
    exact h2
  have hEsub : IsSubnormal E ⊤ := isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hRsub : IsSubnormal (R ⊓ C) C := by
    have := isSubnormal_inf (isSubnormal_trans hRE hEsub) C
    rwa [top_inf_eq] at this
  have hMsub' : IsSubnormal ((K ⊓ C).subgroupOf C) ⊤ :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff inf_le_right).mpr hKsub
  have hTsub' : IsSubnormal ((R ⊓ C).subgroupOf C) ⊤ :=
    (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff inf_le_right).mpr hRsub
  rcases TwoComponentSubnormal.contains_or_normalizes_core _ _ hL hMsub' with hLM | ⟨hMN, hMcomm⟩
  · exfalso
    refine hKL fun x hx => ?_
    have : (⟨x, hLC hx⟩ : ↥C) ∈ (K ⊓ C).subgroupOf C := hLM (Subgroup.mem_subgroupOf.mpr hx)
    exact (Subgroup.mem_subgroupOf.mp this).1
  rcases TwoComponentSubnormal.contains_or_normalizes_core _ _ hL hTsub' with hLT | ⟨hTN, hTcomm⟩
  · intro x hx
    have : (⟨x, hLC hx⟩ : ↥C) ∈ (R ⊓ C).subgroupOf C := hLT (Subgroup.mem_subgroupOf.mpr hx)
    exact (Subgroup.mem_subgroupOf.mp this).1.2
  · exfalso
    have hLMT : L.subgroupOf C ≤ (K ⊓ C).subgroupOf C ⊔ (R ⊓ C).subgroupOf C := by
      rw [← Subgroup.subgroupOf_sup inf_le_right inf_le_right]
      exact fun x hx => hLderiv hx
    have hbot := eq_bot_of_le_sup_of_commutator_le_oddCoreIn (TwoComponents.perfect hL) hLMT hMN hTN
      hMcomm hTcomm
    have hz : (⟨z, hLC hzL⟩ : ↥C) ∈ L.subgroupOf C := Subgroup.mem_subgroupOf.mpr hzL
    rw [hbot, Subgroup.mem_bot] at hz
    exact hz1 (congrArg Subtype.val hz)

theorem exists_isTwoComponent_of_corefree (hX : componentClassificationOddCore X = ⊥) {z : X}
    {L : Subgroup X} (hz1 : z ≠ 1) (hzL : z ∈ L) (hLC : L ≤ Subgroup.centralizer ({z} : Set X))
    (hL : TwoComponents.IsTwoComponent (L.subgroupOf (Subgroup.centralizer ({z} : Set X))))
    (hlayer : L ≤ TwoLayer.subgroup X) :
    ∃ K : Subgroup X, TwoComponents.IsTwoComponent K ∧ L ≤ K := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hLperf, -⟩ := twoComponent_data hLC hL
  have key : ∀ K, TwoComponents.IsTwoComponent K → L ≤ Subgroup.centralizer (K : Set X) :=
    fun K hK => le_centralizer_of_not_le hX hz1 hzL hLC hL hlayer hK (hcon K hK)
  have hE : TwoLayer.subgroup X ≤ Subgroup.centralizer (L : Set X) :=
    sSup_le fun K hK => Subgroup.le_centralizer_iff.mp (key K hK)
  have habel : ⁅L, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hE (hlayer hx)) y hy)
  have hself : ⁅L, L⁆ = L := by
    have : Group.IsPerfect L := ⟨hLperf⟩
    exact Subgroup.commutator_eq_self
  have hbot : L = ⊥ := by rw [← hself, habel]
  have hz : z ∈ (⊥ : Subgroup X) := hbot ▸ hzL
  exact hz1 (Subgroup.mem_bot.mp hz)

end Corefree

section General

variable {W : Type*} [Group W] [Finite W]

theorem oddCore_le_normalizer_of_isTwoComponent {K : Subgroup W}
    (hK : TwoComponents.IsTwoComponent K) :
    componentClassificationOddCore W ≤ Subgroup.normalizer (K : Set W) := by
  have hOsub : IsSubnormal (componentClassificationOddCore W) ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hKnt : ¬ K ≤ componentClassificationOddCore W := by
    intro h
    have hodd : Odd (Nat.card K) :=
      (OddCore.odd_card W).of_dvd_nat (Subgroup.card_dvd_of_le h)
    have hbot := eq_bot_of_perfect_of_odd (TwoComponents.perfect hK) hodd
    exact (Subgroup.nontrivial_iff_ne_bot K).mp (TwoComponents.nontrivial hK) hbot
  rcases TwoComponentSubnormal.contains_or_normalizes_core K _ hK hOsub with h | ⟨h, -⟩
  · exact absurd h hKnt
  · exact h

theorem le_of_perfect_of_map_le {K L : Subgroup W} (hK : TwoComponents.IsTwoComponent K)
    (hperf : commutator L = ⊤)
    (hmap : L.map (QuotientGroup.mk' (componentClassificationOddCore W)) ≤
      K.map (QuotientGroup.mk' (componentClassificationOddCore W))) : L ≤ K := by
  set O : Subgroup W := componentClassificationOddCore W with hO
  let π : W →* W ⧸ O := QuotientGroup.mk' O
  have hON := oddCore_le_normalizer_of_isTwoComponent hK
  set N : Subgroup W := (K.map π).comap π with hN
  have hKN : K ≤ N := Subgroup.le_comap_map π K
  have hLN : L ≤ N := fun x hx => hmap (Subgroup.mem_map_of_mem π hx)
  have hdecomp : ∀ x ∈ N, ∃ k ∈ K, x * k⁻¹ ∈ O := fun x hx => by
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    refine ⟨k, hk, (QuotientGroup.eq_one_iff _).mp ?_⟩
    change π (x * k⁻¹) = 1
    have : π (x * k⁻¹) = π x * (π k)⁻¹ := by rw [map_mul, map_inv]
    rw [this, hkx, mul_inv_cancel]
  have hNN : N ≤ Subgroup.normalizer (K : Set W) := fun x hx => by
    obtain ⟨k, hk, hko⟩ := hdecomp x hx
    have : x = (x * k⁻¹) * k := by group
    rw [this]
    exact Subgroup.mul_mem _ (hON hko) (Subgroup.le_normalizer hk)
  have hOK : O ≤ N := fun o ho => by
    have : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    show π o ∈ K.map π
    rw [this]
    exact Subgroup.one_mem _
  have : (K.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hNN
  let g : ↥O →* ↥N ⧸ K.subgroupOf N :=
    (QuotientGroup.mk' (K.subgroupOf N)).comp (Subgroup.inclusion hOK)
  have hg : Function.Surjective g := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf N) y
    obtain ⟨k, hk, hko⟩ := hdecomp x.1 x.2
    refine ⟨⟨x.1 * k⁻¹, hko⟩, ?_⟩
    change (QuotientGroup.mk' (K.subgroupOf N)) ⟨x.1 * k⁻¹, hOK hko⟩ =
      (QuotientGroup.mk' (K.subgroupOf N)) x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have : ((⟨x.1 * k⁻¹, hOK hko⟩ : ↥N)⁻¹ * x : ↥N).1 = k := by
      change (x.1 * k⁻¹)⁻¹ * x.1 = k
      group
    rw [this]
    exact hk
  have hoddN : Odd (Nat.card (↥N ⧸ K.subgroupOf N)) :=
    (OddCore.odd_card W).of_dvd_nat (Subgroup.card_dvd_of_surjective hg)
  let ψ : ↥L →* ↥N ⧸ K.subgroupOf N :=
    (QuotientGroup.mk' (K.subgroupOf N)).comp (Subgroup.inclusion hLN)
  have hLperf : Group.IsPerfect L := ⟨hperf⟩
  have hrangeperf : Group.IsPerfect ψ.range :=
    Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hrangeodd : Odd (Nat.card ψ.range) :=
    hoddN.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hbot := eq_bot_of_perfect_of_odd (Group.IsPerfect.commutator_eq_top (G := ψ.range)) hrangeodd
  intro l hl
  have h1 : ψ ⟨l, hl⟩ ∈ ψ.range := ⟨⟨l, hl⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : (⟨l, hLN hl⟩ : ↥N) ∈ K.subgroupOf N := (QuotientGroup.eq_one_iff _).mp h1
  exact Subgroup.mem_subgroupOf.mp h2

theorem exists_isTwoComponent_of_mem_twoLayer {z : W} {L : Subgroup W} (hz : orderOf z = 2)
    (hzL : z ∈ L) (hLC : L ≤ Subgroup.centralizer ({z} : Set W))
    (hL : TwoComponents.IsTwoComponent (L.subgroupOf (Subgroup.centralizer ({z} : Set W))))
    (hlayer : L ≤ TwoLayer.subgroup W) :
    ∃ K : Subgroup W, TwoComponents.IsTwoComponent K ∧ L ≤ K := by
  set O : Subgroup W := componentClassificationOddCore W with hO
  let π : W →* W ⧸ O := QuotientGroup.mk' O
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hπk : Odd (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact OddCore.odd_card W
  have hpg : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz]; simp)
  obtain ⟨-, hLperf, -⟩ := twoComponent_data hLC hL
  set z' : W ⧸ O := π z with hz'def
  have hz' : orderOf z' = 2 := orderOf_mk_oddCore_eq_two hz
  have hz'1 : z' ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz'
    omega
  have hcore : componentClassificationOddCore (W ⧸ O) = ⊥ := OddCore.quotient_corefree W
  set C : Subgroup W := Subgroup.centralizer ({z} : Set W) with hC
  set C' : Subgroup (W ⧸ O) := Subgroup.centralizer ({z'} : Set (W ⧸ O)) with hC'
  have hmapC : C.map π = C' := map_centralizer_singleton_eq (OddCore.odd_card W) hpg
  have hρ : ∀ x : ↥C, π x ∈ C' := fun x => by
    rw [← hmapC]
    exact ⟨x, x.2, rfl⟩
  let ρ : ↥C →* ↥C' := (π.comp C.subtype).codRestrict C' hρ
  have hρs : Function.Surjective ρ := fun y => by
    have hy : (y : W ⧸ O) ∈ C.map π := by
      rw [hmapC]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hρk : Odd (Nat.card ρ.ker) := by
    have hk : ρ.ker = π.ker.comap C.subtype := by
      ext x
      change ρ x = 1 ↔ π x.1 = 1
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hk]
    exact hπk.of_dvd_nat (Subgroup.card_comap_dvd_of_injective _ C.subtype C.subtype_injective)
  have hLimg : (L.subgroupOf C).map ρ = (L.map π).subgroupOf C' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr ⟨x.1, Subgroup.mem_subgroupOf.mp hx, rfl⟩
    · intro hy
      obtain ⟨l, hl, hly⟩ := Subgroup.mem_subgroupOf.mp hy
      exact ⟨⟨l, hLC hl⟩, Subgroup.mem_subgroupOf.mpr hl, Subtype.ext hly⟩
  have hL' : TwoComponents.IsTwoComponent ((L.map π).subgroupOf C') := by
    rw [← hLimg]
    exact OddKernelTwoComponents.image ρ hρs hρk _ hL
  have hLC' : L.map π ≤ C' := hmapC ▸ Subgroup.map_mono hLC
  have hlayer' : L.map π ≤ TwoLayer.subgroup (W ⧸ O) := by
    rw [← TwoLayerTransport.image_of_odd_kernel π hπs hπk]
    exact Subgroup.map_mono hlayer
  obtain ⟨K', hK', hLK'⟩ := exists_isTwoComponent_of_corefree hcore hz'1
    (Subgroup.mem_map_of_mem π hzL) hLC' hL' hlayer'
  obtain ⟨K, hK, hKmap⟩ := OddKernelTwoComponents.exists_lift π hπs hπk K' hK'
  exact ⟨K, hK, le_of_perfect_of_map_le hK hLperf (hKmap ▸ hLK')⟩

theorem existsUnique_isTwoComponent_of_mem_twoLayer {z : W} {L : Subgroup W} (hz : orderOf z = 2)
    (hzL : z ∈ L) (hperf : commutator L = ⊤) (hsub : IsSubnormal L (Subgroup.centralizer {z}))
    (hq : CFSG.Open.IsQuasisimple (L ⧸ componentClassificationOddCore L))
    (hlayer : L ≤ TwoLayer.subgroup W) :
    ∃! K : Subgroup W, TwoComponents.IsTwoComponent K ∧ L ≤ K := by
  have hLC : L ≤ Subgroup.centralizer ({z} : Set W) := isSubnormal_le hsub
  have hne : L ≠ ⊥ := fun h => by
    have : z ∈ (⊥ : Subgroup W) := h ▸ hzL
    have hz1 : z = 1 := Subgroup.mem_bot.mp this
    rw [hz1, orderOf_one] at hz
    omega
  obtain ⟨K, hK, hLK⟩ := exists_isTwoComponent_of_mem_twoLayer hz hzL hLC
    (isTwoComponent_subgroupOf_of_perfect_of_le hLC hsub hperf hq) hlayer
  exact ⟨K, ⟨hK, hLK⟩, fun K' hK' =>
    (eq_of_isTwoComponent_of_perfect_le hK hK'.1 hLK hK'.2 hperf hne).symm⟩

theorem existsUnique_isTwoComponent_of_l2PrimeBalance (hLB : L2PrimeBalance) {W : Type}
    [Group W] [Finite W] {z : W} {L : Subgroup W} (hz : orderOf z = 2) (hzL : z ∈ L)
    (hperf : commutator L = ⊤) (hsub : IsSubnormal L (Subgroup.centralizer {z}))
    (hq : CFSG.Open.IsQuasisimple (L ⧸ componentClassificationOddCore L)) :
    ∃! K : Subgroup W, TwoComponents.IsTwoComponent K ∧ L ≤ K := by
  have hA : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz]; simp)
  have hXz : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup W) : Set W) =
      Subgroup.centralizer ({z} : Set W) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hlayer : L ≤ TwoLayer.subgroup W :=
    le_twoLayer_of_l2PrimeBalance hLB hA (by rw [hXz]; exact isSubnormal_le hsub)
      (by rw [hXz]; exact hsub) hperf hq
  exact existsUnique_isTwoComponent_of_mem_twoLayer hz hzL hperf hsub hq hlayer

end General

section Subgroup

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem memberData_subgroupOf {Y L : Subgroup X} {z : X} (hz : orderOf z = 2) (hLY : L ≤ Y)
    (hzL : z ∈ L) (hperf : commutator L = ⊤)
    (hsub : IsSubnormal L (Subgroup.centralizer {z} ⊓ Y))
    (hq : CFSG.Open.IsQuasisimple (L ⧸ componentClassificationOddCore L)) :
    orderOf (⟨z, hLY hzL⟩ : ↥Y) = 2 ∧ (⟨z, hLY hzL⟩ : ↥Y) ∈ L.subgroupOf Y ∧
      commutator (L.subgroupOf Y) = ⊤ ∧
      CFSG.Open.IsQuasisimple
        ((L.subgroupOf Y) ⧸ componentClassificationOddCore (L.subgroupOf Y)) ∧
      IsSubnormal (L.subgroupOf Y) (Subgroup.centralizer {(⟨z, hLY hzL⟩ : ↥Y)}) := by
  let e : (L.subgroupOf Y) ≃* L := Subgroup.subgroupOfEquivOfLe hLY
  refine ⟨by rw [Subgroup.orderOf_mk]; exact hz, Subgroup.mem_subgroupOf.mpr hzL, ?_, ?_, ?_⟩
  · have : Group.IsPerfect L := ⟨hperf⟩
    have : Group.IsPerfect (L.subgroupOf Y) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  · exact Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore (L.subgroupOf Y))
        (componentClassificationOddCore L) e (OddCore.equiv_invariant e)) hq
  · have h := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf hsub Y
    rwa [subgroupOf_centralizer_inf (hLY hzL)] at h

theorem exists_isTwoComponent_of_subgroup {Y L : Subgroup X} {z : X} (hz : orderOf z = 2)
    (hLY : L ≤ Y) (hzL : z ∈ L) (hperf : commutator L = ⊤)
    (hsub : IsSubnormal L (Subgroup.centralizer {z} ⊓ Y))
    (hq : CFSG.Open.IsQuasisimple (L ⧸ componentClassificationOddCore L))
    (hlayer : L.subgroupOf Y ≤ TwoLayer.subgroup ↥Y) :
    ∃ K : Subgroup X, K ≤ Y ∧ TwoComponents.IsTwoComponent (K.subgroupOf Y) ∧ L ≤ K := by
  obtain ⟨hzY, hzLY, hperfY, hqY, hsubY⟩ := memberData_subgroupOf hz hLY hzL hperf hsub hq
  obtain ⟨KY, hKY, hLKY⟩ := exists_isTwoComponent_of_mem_twoLayer hzY hzLY
    (isSubnormal_le hsubY)
    (isTwoComponent_subgroupOf_of_perfect_of_le (isSubnormal_le hsubY) hsubY hperfY hqY) hlayer
  refine ⟨KY.map Y.subtype, Subgroup.map_subtype_le _, ?_, fun x hx => ?_⟩
  · have h : (KY.map Y.subtype).subgroupOf Y = KY :=
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective KY
    rw [h]
    exact hKY
  · exact ⟨⟨x, hLY hx⟩, hLKY (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem exists_isTwoComponent_of_l2PrimeBalance_subgroup (hLB : L2PrimeBalance) {X : Type}
    [Group X] [Finite X] {Y L : Subgroup X} {z : X} (hz : orderOf z = 2) (hLY : L ≤ Y)
    (hzL : z ∈ L) (hperf : commutator L = ⊤)
    (hsub : IsSubnormal L (Subgroup.centralizer {z} ⊓ Y))
    (hq : CFSG.Open.IsQuasisimple (L ⧸ componentClassificationOddCore L)) :
    ∃ K : Subgroup X, K ≤ Y ∧ TwoComponents.IsTwoComponent (K.subgroupOf Y) ∧ L ≤ K := by
  obtain ⟨hzY, hzLY, hperfY, hqY, hsubY⟩ := memberData_subgroupOf hz hLY hzL hperf hsub hq
  obtain ⟨KY, ⟨hKY, hLKY⟩, -⟩ :=
    existsUnique_isTwoComponent_of_l2PrimeBalance hLB hzY hzLY hperfY hsubY hqY
  refine ⟨KY.map Y.subtype, Subgroup.map_subtype_le _, ?_, fun x hx => ?_⟩
  · have h : (KY.map Y.subtype).subgroupOf Y = KY :=
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective KY
    rw [h]
    exact hKY
  · exact ⟨⟨x, hLY hx⟩, hLKY (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem exists_isTwoComponent_of_le_centralizer (hLB : L2PrimeBalance) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {z t : G} (hz : orderOf z = 2) (hzL : z ∈ L)
    (hperf : commutator L = ⊤) (hsub : IsSubnormal L (Subgroup.centralizer {z}))
    (hq : CFSG.Open.IsQuasisimple (L ⧸ componentClassificationOddCore L))
    (hLt : L ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ K : Subgroup G, K ≤ Subgroup.centralizer ({t} : Set G) ∧
      TwoComponents.IsTwoComponent (K.subgroupOf (Subgroup.centralizer ({t} : Set G))) ∧
        L ≤ K := by
  refine exists_isTwoComponent_of_l2PrimeBalance_subgroup hLB hz hLt hzL hperf ?_ hq
  have := isSubnormal_inf hsub (Subgroup.centralizer ({t} : Set G))
  rwa [inf_eq_left.mpr hLt] at this

theorem eq_of_isTwoComponent_subgroup_of_perfect_le {Y K K' L : Subgroup X} (hKY : K ≤ Y)
    (hK'Y : K' ≤ Y) (hLY : L ≤ Y) (hK : TwoComponents.IsTwoComponent (K.subgroupOf Y))
    (hK' : TwoComponents.IsTwoComponent (K'.subgroupOf Y)) (hLK : L ≤ K) (hLK' : L ≤ K')
    (hperf : commutator L = ⊤) (hne : L ≠ ⊥) : K = K' := by
  let e : (L.subgroupOf Y) ≃* L := Subgroup.subgroupOfEquivOfLe hLY
  have hperfY : commutator (L.subgroupOf Y) = ⊤ := by
    have : Group.IsPerfect L := ⟨hperf⟩
    have : Group.IsPerfect (L.subgroupOf Y) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hneY : L.subgroupOf Y ≠ ⊥ := fun h => hne (by
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hLY hx⟩ : ↥Y) ∈ L.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this))
  have h := eq_of_isTwoComponent_of_perfect_le hK hK' (fun x hx => hLK hx) (fun x hx => hLK' hx)
    hperfY hneY
  have h2 := Subgroup.subgroupOf_inj.mp h
  rwa [inf_eq_left.mpr hKY, inf_eq_left.mpr hK'Y] at h2

end Subgroup

section Members

variable {Y : Type*} [Group Y] [Finite Y]

theorem isQuasisimple_of_members_in_components (hO : componentClassificationOddCore Y = ⊥)
    {Λ : Set (Subgroup Y)} (hne : Λ.Nonempty) (hgen : ⨆ L ∈ Λ, L = ⊤)
    (hmem : ∀ L ∈ Λ, ∃ K : Subgroup Y, TwoComponents.IsTwoComponent K ∧ L ≤ K)
    (hconn : Generic.NonCommConnected Λ) : CFSG.Open.IsQuasisimple Y := by
  obtain ⟨L₀, hL₀⟩ := hne
  obtain ⟨K₀, hK₀, hL₀K₀⟩ := hmem L₀ hL₀
  have hK₀q : CFSG.Open.IsQuasisimple K₀ := (TwoComponents.ordinary_of_corefree hO hK₀).2.2
  have hall : ∀ L : ↥Λ, (L : Subgroup Y) ≤ K₀ := by
    intro L
    have hrt := (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (hconn.preconnected ⟨L₀, hL₀⟩ L)
    induction hrt with
    | refl => exact hL₀K₀
    | @tail b c _ hadj ih =>
      obtain ⟨K', hK', hcK'⟩ := hmem (c : Subgroup Y) c.2
      by_cases hKK : K' = K₀
      · exact hKK ▸ hcK'
      · exfalso
        obtain ⟨-, hnc⟩ := Generic.nonCommGraph_adj.mp hadj
        refine hnc fun x hx y hy => ?_
        have hcomm := TwoComponentInteraction.commutes_of_quasisimple_left K₀ K' hK₀ hK'
          (Ne.symm hKK) hK₀q
        exact (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm (ih hx)) y (hcK' hy)).symm
  have htop : K₀ = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact iSup₂_le fun L hL => hall ⟨L, hL⟩
  rw [htop] at hK₀q
  exact Components.quasisimple_of_equiv Subgroup.topEquiv.symm hK₀q

theorem isQuasisimple_of_members (hLB : L2PrimeBalance) {Y : Type} [Group Y] [Finite Y]
    (hO : componentClassificationOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hne : Λ.Nonempty)
    (hgen : ⨆ L ∈ Λ, L = ⊤)
    (hmem : ∀ L ∈ Λ, ∃ z : Y, orderOf z = 2 ∧ z ∈ L ∧ commutator L = ⊤ ∧
      IsSubnormal L (Subgroup.centralizer {z}) ∧
      CFSG.Open.IsQuasisimple (L ⧸ componentClassificationOddCore L))
    (hconn : Generic.NonCommConnected Λ) : CFSG.Open.IsQuasisimple Y :=
  isQuasisimple_of_members_in_components hO hne hgen
    (fun L hL => by
      obtain ⟨z, hz, hzL, hperf, hsub, hq⟩ := hmem L hL
      obtain ⟨K, hK, -⟩ := existsUnique_isTwoComponent_of_l2PrimeBalance hLB hz hzL hperf hsub hq
      exact ⟨K, hK.1, hK.2⟩) hconn

end Members

end CFSG.ClassicalInvolution
