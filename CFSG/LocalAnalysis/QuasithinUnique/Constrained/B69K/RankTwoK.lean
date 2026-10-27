module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs
public import CFSG.Quasithin.Background.GoldschmidtB69DeepN2dA
public import CFSG.Quasithin.Background.GoldschmidtB69DeepHypB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux
public import CFSG.Quasithin.Background.FFC11D
public import CFSG.Quasithin.Background.FFC11F
public import CFSG.Quasithin.Background.GoldschmidtB69DeepSp4
public import CFSG.Quasithin.Background.GoldschmidtB69DeepN2c

public section

namespace CFSG.Quasithin

namespace B69K

section SL3K

open CFSG.Assembly.LowTwoRank H H.SL3Pair
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open B6
open scoped commutatorElement
open CFSG.Quasithin.B69

theorem noRankTwoSL3K_of {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X T M A L : Subgroup (MulAut V)} (hH : CompHypK X T M A L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V))
    (hc : B42Case2 (autSec (L ⊔ A) W (W ⊓ fixV L)) (autSec L W (W ⊓ fixV L))) : False := by
  obtain ⟨-, hmp, -, -, -, hA, hL, hLA⟩ := hH
  obtain ⟨-, ⟨n, hn⟩, -⟩ := hc
  obtain ⟨K, hKf, hKfin, hK, r, hr, e₁, he₁⟩ := n2_natural_data hW hn
  have hn1 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn1 hK
  have h2K : 2 ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self 2 (by omega)
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLX : L ≤ X := hL.1
  have : Finite (MulAut V) := MulEquiv.finite_left
  let π₀ : ↥L →* projectiveSL 3 K := (proj 3 K).comp ((slEquiv K).symm.toMonoidHom.comp r)
  have hπ₀ : Function.Surjective π₀ :=
    (proj_surjective 3 K).comp ((slEquiv K).symm.surjective.comp hr)
  have : Nontrivial (projectiveSL 3 K) := nontrivial_projectiveSL_three h2K
  have hker₀ : π₀.ker = Subgroup.center ↥L :=
    ker_eq_center_of_surj hLq center_projectiveSL_three π₀ hπ₀
  have hLhat : CFSG.Open.IsComponentOf (L.subgroupOf X) ⊤ := isComponentOf_subgroupOf hL
  let e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  let πh : ↥(L.subgroupOf X) →* projectiveSL 3 K := π₀.comp e0.toMonoidHom
  have hπh : Function.Surjective πh := hπ₀.comp e0.surjective
  have hkerh : πh.ker = Subgroup.center ↥(L.subgroupOf X) :=
    ker_eq_center_of_surj hLhat.2.2 center_projectiveSL_three πh hπh
  obtain ⟨t, -, htN, hall⟩ := exists_swap swapGeo_sl3 (even_card_projectiveSL_three h2K)
    hmp.subgroupOf hLhat πh hπh hkerh
  have ht : ∀ x ∈ L, (t : MulAut V) * x * (t : MulAut V)⁻¹ ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp htN ⟨x, hLX hx⟩).mp hx'
    exact this
  have ht' : ∀ x ∈ L, (t : MulAut V)⁻¹ * x * (t : MulAut V) ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) ⟨x, hLX hx⟩).mp hx'
    exact this
  have htV : (t : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    mem_normalizer_of_forall_mem ht ht'
  obtain ⟨thb, hthb⟩ := exists_aut_of_ker_eq π₀ hπ₀ (indAut L (t : MulAut V)) (by
    intro l
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker₀]
    exact mem_center_map_iff _ l)
  have hind : ∀ l l' : ↥L, (l' : MulAut V) = (t : MulAut V) * l * (t : MulAut V)⁻¹ →
      indAut L (t : MulAut V) l = l' := by
    intro l l' hl'
    apply Subtype.ext
    rw [coe_indAut_apply htV, hl']
  have hnot : ¬ TypePres thb := by
    refine hall thb fun l l' hl' => ?_
    have h1 : indAut L (t : MulAut V) (e0 l) = e0 l' := by
      apply hind
      show ((l' : ↥X) : MulAut V) = _
      rw [hl']
      rfl
    show thb (π₀ (e0 l)) = π₀ (e0 l')
    rw [hthb, h1]
  exact false_of_twist_ff hV hA hLq hLA hn1 hK r hr hW e₁ he₁ (t : MulAut V) ht ht' thb
    (fun l l' hl' => by
      have := hthb l
      rw [hind l l' hl'] at this
      exact this) hnot

end SL3K

section Sp4K

open CFSG.Assembly.LowTwoRank H H.PairG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (proj_surjective)
open CFSG.QuasithinUnique.Lin2.Five (tauSp projEquiv)
open B6
open CFSG.Quasithin.B69

theorem noRankTwoSp4K :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (X T M A L : Subgroup (MulAut V)), CompHypK X T M A L →
        ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) → ¬ B42Case3 (wtLA A L W) (wtL L W) := by
  intro V _ _ hV X T M A L hH W hW hc
  obtain ⟨-, hmp, -, -, -, hA, hL, hLA⟩ := hH
  obtain ⟨⟨n, hnat, hHL⟩, -⟩ := hc
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hn0 : 1 ≤ n := by
    obtain ⟨K, hKf, hKfin, hK, -⟩ := hnat
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  by_cases hn1 : n = 1
  · subst hn1
    have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
    have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
      B19Aux.conj_mem_of_le_normalizer hAnL ha hl
    have hA₁ := a_stab_irr hV hA hLq hLA hW
    have hAW : A ≤ stabSub W := B1.le_stabSub_of_invariant hA₁
    have hAZ : A ≤ stabSub (W ⊓ fixV L) :=
      B1.le_stabSub_of_invariant (isInv_inf hA₁ (B1Red.fixV_inv_of_normalizes hAn))
    obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
    have hGJ : wtLA A L W ≤ ffJ (wtLA A L W) :=
      FFC.le_of_binaryNaturalSp4_one
        (fun g hg h hh => (Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_ffJ _ hg) _).1 hh) hnat
    have hLH : wtL L W ≤ ffJ (wtLA A L W) := (autSec_mono le_sup_left W _).trans hGJ
    have hnormH := normal_autSec_subgroupOf hAnL (sup_le hLW hAW) (sup_le hLZ hAZ)
      (B6.ffJ_le (wtLA A L W))
    obtain ⟨S⟩ := exists_twist_data_a6 hmp hL hW hLH hnat hnormH
    exact false_of_twist_lt hV hA hLq hLA le_rfl (by simp) hW S
  · have hHL' : ffJ (wtLA A L W) = wtL L W := hHL (by omega)
    have hnat' : BinaryNaturalSp4 (wtL L W) ⊤ ⊥ n := by
      rw [← hHL']
      exact hnat
    obtain ⟨K, _, _, _, hK, ⟨S⟩⟩ := exists_twist_data_sp4 hmp hL hW (by omega) hnat'
    exact false_of_twist_lt hV hA hLq hLA hn0 hK hW S

end Sp4K

section A6K

open B6 B42Alt6
open CFSG.Quasithin.B69

theorem noRankTwoA6K :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (X T M A L : Subgroup (MulAut V)), CompHypK X T M A L →
        ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
          ∀ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) →
            IsFFStarOffender (wtLA A L W) B → ¬ B42Case6 (wtLA A L W) (wtL L W) B := by
  intro V _ _ hV X T M A L hH W hW B hBA hBo hc
  obtain ⟨-, hmp, -, -, -, hA, hL, hLA⟩ := hH
  obtain ⟨-, hAlt, -, hq, -⟩ := hc
  obtain ⟨π, hπ⟩ : ∃ π : ↥(alternatingGroup (Fin 6)) →* ↥(wtL L W),
      (FFModel.altDn 6).RealizesVia (wtL L W) ⊤ ⊥ π := hAlt
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  obtain ⟨Θ, hΘ⟩ := exists_n6Equiv_of_altDn hπ
  have hρπ : ∀ (γ : ↥(alternatingGroup (Fin 6))) (w : Sec W (W ⊓ fixV L)),
      rhoOf Θ (γ : Equiv.Perm (Fin 6)) w = ((π γ : ↥(wtL L W)) : MulAut _) w := by
    intro γ w
    apply Θ.injective
    rw [rhoOf_apply, hΘ]
  have hρA : (alternatingGroup (Fin 6)).map (rhoOf Θ) = wtL L W := by
    ext x
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      have : rhoOf Θ γ = ((π ⟨γ, hγ⟩ : ↥(wtL L W)) : MulAut _) :=
        MulEquiv.ext fun w => hρπ ⟨γ, hγ⟩ w
      rw [this]
      exact (π ⟨γ, hγ⟩).2
    · intro hx
      obtain ⟨γ, hγ⟩ : ∃ γ : ↥(alternatingGroup (Fin 6)), π γ = ⟨x, hx⟩ := hπ.1 ⟨x, hx⟩
      refine ⟨γ, γ.2, ?_⟩
      have : rhoOf Θ γ = ((π γ : ↥(wtL L W)) : MulAut _) := MulEquiv.ext fun w => hρπ γ w
      rw [this, hγ]
  let M₆ : N6Model (wtL L W) :=
    ⟨Θ, rhoOf Θ, rhoOf_injective Θ, rhoOf_apply Θ, hρA⟩
  have hrange : ∀ σ, M₆.ρ σ ∈ M₆.ρ.range := fun σ => ⟨σ, rfl⟩
  have hn : BinaryNaturalSp4 M₆.ρ.range ⊤ ⊥ 1 :=
    M₆.binaryNaturalSp4 hrange (fun h ⟨σ, hσ⟩ => ⟨σ, hσ⟩)
  have hLH : wtL L W ≤ M₆.ρ.range := by
    intro x hx
    obtain ⟨γ, -, rfl⟩ := M₆.mem_L_iff.1 hx
    exact ⟨γ, rfl⟩
  have hnormH : ((wtL L W).subgroupOf M₆.ρ.range).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    obtain ⟨γ, hγ, hγn⟩ := M₆.mem_L_iff.1 hn'
    obtain ⟨σ, hσ⟩ := g.2
    rw [M₆.mem_L_iff]
    refine ⟨σ * γ * σ⁻¹, (alternatingGroup.normal (α := Fin 6)).conj_mem γ hγ σ, ?_⟩
    show M₆.ρ (σ * γ * σ⁻¹) = (g : MulAut _) * (n : MulAut _) * (g : MulAut _)⁻¹
    rw [map_mul, map_mul, map_inv, hσ, hγn]
  obtain ⟨S⟩ := exists_twist_data_a6 hmp hL hW hLH hn hnormH
  obtain ⟨W₂, hW₂, hne, -⟩ := exists_twist_member_sp4 S.r hW S.e₁ S.he₁ S.t S.ht S.ht' S.htw S.hniso
  exact false_of_one_le_rAV hV hA hLq hLA hW hW₂ hne
    (one_le_rAV_of_qOf hV hA hLq hLA hW hq.ge)

end A6K

section SecDataK

open CFSG.Open
open scoped commutatorElement
open CFSG.Quasithin.B69

variable {V : Type} [CommGroup V] [Finite V]

theorem sectionFittingDataK (hV : ∀ v : V, v ^ 2 = 1) {X T M A L : Subgroup (MulAut V)}
    (hH : CompHypK X T M A L) {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) :
    ∃ ℓ : ↥L →* ↥(autSec L W (W ⊓ fixV L)), Function.Surjective ℓ ∧
      ℓ.ker ≤ Subgroup.center ↥L ∧ CFSG.IsQuasisimple ↥(autSec L W (W ⊓ fixV L)) ∧
      XMod.IsIrrSec ↥(autSec L W (W ⊓ fixV L)) (⊥ : Subgroup (Sec W (W ⊓ fixV L))) ⊤ ∧
      quasithinGenFitting (autSec (L ⊔ A) W (W ⊓ fixV L)) = autSec L W (W ⊓ fixV L) ∧
      (∀ g ∈ autSec (L ⊔ A) W (W ⊓ fixV L), ∀ l ∈ autSec L W (W ⊓ fixV L),
        g * l * g⁻¹ ∈ autSec L W (W ⊓ fixV L)) ∧
      ∀ (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub (W ⊓ fixV L)) (l : ↥L),
        ((ℓ l : ↥(autSec L W (W ⊓ fixV L))) : MulAut (Sec W (W ⊓ fixV L))) =
          B5.secHom L hLW hLU l := by
  obtain ⟨-, -, -, -, -, hA, hL, hLA⟩ := hH
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hAel : IsElemAbelian2 A := hA.1.2.2.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  have hAW := a_stab_irr hV hA hLq hLA hW
  have hAZ : ∀ b ∈ A, ∀ w ∈ W ⊓ fixV L, b w ∈ W ⊓ fixV L :=
    isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn)
  have hAWs : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAZs : A ≤ stabSub (W ⊓ fixV L) := B1.le_stabSub_of_invariant hAZ
  have hMW : L ⊔ A ≤ stabSub W := sup_le hLW hAWs
  have hMZ : L ⊔ A ≤ stabSub (W ⊓ fixV L) := sup_le hLZ hAZs
  have hsupn : ∀ y ∈ L ⊔ A, ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
    intro y hy l hl
    obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hy
    have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hl' (hAn a ha l hl)) (L.inv_mem hl')
  have hsq2 : ∀ y ∈ L ⊔ A, y ^ 2 ∈ L := B1Red.sq_mem_of_mem_sup hAnL hAel.2
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  obtain ⟨ℓ, hℓs, hℓa⟩ : ∃ ℓ : ↥L →* ↥(autSec L W (W ⊓ fixV L)), Function.Surjective ℓ ∧
      ∀ l : ↥L, ((ℓ l : ↥(autSec L W (W ⊓ fixV L))) : MulAut (Sec W (W ⊓ fixV L))) =
        B5.secHom L hLW hLZ l := by
    refine ⟨(B5.secHom L hLW hLZ).codRestrict (autSec L W (W ⊓ fixV L)) (fun l => ?_), ?_,
      fun l => rfl⟩
    · rw [← B5.range_secHom L hLW hLZ]
      exact ⟨l, rfl⟩
    · intro y
      have hy : (y : MulAut (Sec W (W ⊓ fixV L))) ∈ (B5.secHom L hLW hLZ).range := by
        rw [B5.range_secHom L hLW hLZ]
        exact y.2
      obtain ⟨l, hl⟩ := hy
      exact ⟨l, Subtype.ext hl⟩
  have hmapL := B5.map_secHom_eq_autSec (L ⊔ A) hMW hMZ (le_sup_left : L ≤ L ⊔ A)
  have hrange := B5.range_secHom (L ⊔ A) hMW hMZ
  have hLG : autSec L W (W ⊓ fixV L) ≤ autSec (L ⊔ A) W (W ⊓ fixV L) :=
    autSec_mono le_sup_left W _
  have hLbn : ∀ g ∈ autSec (L ⊔ A) W (W ⊓ fixV L), ∀ l ∈ autSec L W (W ⊓ fixV L),
      g * l * g⁻¹ ∈ autSec L W (W ⊓ fixV L) := by
    intro g hg l hl
    rw [← hrange] at hg
    obtain ⟨m, rfl⟩ := hg
    rw [← hmapL] at hl ⊢
    obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.1 hl
    refine Subgroup.mem_map.2 ⟨m * l' * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf] at hl' ⊢
    exact hsupn m m.2 l' hl'
  have hHb2 : ∀ y ∈ autSec (L ⊔ A) W (W ⊓ fixV L), y ^ 2 ∈ autSec L W (W ⊓ fixV L) := by
    intro y hy
    rw [← hrange] at hy
    obtain ⟨m, rfl⟩ := hy
    rw [← hmapL]
    refine Subgroup.mem_map.2 ⟨m ^ 2, ?_, by simp [map_pow]⟩
    rw [Subgroup.mem_subgroupOf]
    exact hsq2 m m.2
  have hnt : Nontrivial ↥(autSec L W (W ⊓ fixV L)) := nontrivial_autSec hW
  have hne : ℓ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    obtain ⟨x, rfl⟩ := hℓs a
    obtain ⟨y, rfl⟩ := hℓs b
    apply hab
    have hx : x ∈ ℓ.ker := by rw [htop]; trivial
    have hy : y ∈ ℓ.ker := by rw [htop]; trivial
    rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  have hcent : ℓ.ker ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLq ℓ.ker hne
  have hLbq : CFSG.IsQuasisimple ↥(autSec L W (W ⊓ fixV L)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective (B1Red.isQuasisimple_of_open hLq) ℓ hℓs hcent
  obtain ⟨-, -, hlt, hirr⟩ := mem_irrPlus_top_iff.1 hW
  have hIrr : XMod.IsIrrSec ↥(autSec L W (W ⊓ fixV L)) (⊥ : Subgroup (Sec W (W ⊓ fixV L))) ⊤ :=
    B5.isIrrSec_autSec hlt hirr hLW hLZ
  have hO2G : pCoreOf 2 (autSec (L ⊔ A) W (W ⊓ fixV L)) = ⊥ := n1_pCoreOf_eq_bot hS2 hLG hIrr
  have hFstar : quasithinGenFitting (autSec (L ⊔ A) W (W ⊓ fixV L)) = autSec L W (W ⊓ fixV L) :=
    B1Red.quasithinGenFitting_eq_of_two_quot hLG hLbn (B1Red.isQuasisimple_to_open hLbq) hHb2 hO2G
  exact ⟨ℓ, hℓs, hcent, hLbq, hIrr, hFstar, hLbn, fun _ _ l => hℓa l⟩

end SecDataK

section TripleA6K

open CFSG.Open B6
open scoped commutatorElement
open CFSG.Quasithin.B69

theorem noRankTwoTripleA6K :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (X T M A L : Subgroup (MulAut V)), CompHypK X T M A L →
        ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
          ∀ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) →
            IsFFStarOffender (wtLA A L W) B → ¬ B42Case8 (wtLA A L W) (wtL L W) B := by
  intro V _ _ hV X T M A L hH W hW B hBA hB hc
  obtain ⟨ℓ, hℓs, hcent, hLbq, hIrr, hFstar, hLbn, hℓa⟩ := sectionFittingDataK hV hH hW
  obtain ⟨-, hmp, -, -, -, hA, hL, hLA⟩ := hH
  obtain ⟨-, hcard, hq, K, _, _, Γ₀, hK4, -, hhat, -, π, hreal, -⟩ := hc
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  have hS2 : ∀ s : Sec W (W ⊓ fixV L), s ^ 2 = 1 := sq_eq_one_sec hV W (W ⊓ fixV L)
  have hperf : Group.IsPerfect ↥(autSec L W (W ⊓ fixV L)) := hLbq.1
  have hinj : Function.Injective π := natRealizes_injective hreal
  let eπ : ↥Γ₀ ≃* ↥(autSec L W (W ⊓ fixV L)) := MulEquiv.ofBijective π ⟨hinj, hreal.1⟩
  have hcenter : (Subgroup.center ↥Γ₀).map eπ.toMonoidHom =
      Subgroup.center ↥(autSec L W (W ⊓ fixV L)) := Subgroup.map_center_eq eπ
  have hZ : Nat.card ↥(Subgroup.center ↥(autSec L W (W ⊓ fixV L))) = 3 := by
    rw [← hcenter, Subgroup.card_map_of_injective (f := eπ.toMonoidHom) eπ.injective]
    exact hhat.2.1
  let e : ↥(autSec L W (W ⊓ fixV L)) ⧸ Subgroup.center ↥(autSec L W (W ⊓ fixV L)) ≃*
      ↥(alternatingGroup (Fin 6)) :=
    (QuotientGroup.congr _ _ eπ hcenter).symm.trans hhat.2.2.some
  obtain ⟨ρ, hρr, hρx⟩ := Hyp.exists_hyperoval hS2 hcard hperf hZ e
    (CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hIrr)
  have hmem : ∀ l : ↥L, ρ (ℓ l) ∈ alternatingGroup (Fin 6) := fun l => by
    rw [← hρr]
    exact ⟨ℓ l, rfl⟩
  let π₀ : ↥L →* ↥(alternatingGroup (Fin 6)) :=
    (ρ.comp ℓ).codRestrict (alternatingGroup (Fin 6)) hmem
  have hπ₀ : Function.Surjective π₀ := by
    intro y
    have : (y : Equiv.Perm (Fin 6)) ∈ ρ.range := by
      rw [hρr]
      exact y.2
    obtain ⟨m, hm⟩ := this
    obtain ⟨l, rfl⟩ := hℓs m
    exact ⟨l, Subtype.ext hm⟩
  have hcenter6 : Subgroup.center ↥(alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hev : Even (Nat.card ↥(alternatingGroup (Fin 6))) := by
    rw [Sp4Inf.card_alt_six']
    exact ⟨180, by norm_num⟩
  obtain ⟨t, ht, ht', thb, hthb, hnot⟩ :=
    exists_twist_element hmp hL Sp4Inf.swapGeo_alt6 hev hcenter6 π₀ hπ₀
  set W₂ : Subgroup V := W.map (t⁻¹ : MulAut V).toMonoidHom with hW₂
  have hW₂irr : W₂ ∈ IrrPlus L (⊤ : Subgroup V) :=
    irrPlus_map (g := t⁻¹) (fun x hx => by rw [inv_inv]; exact ht' x hx)
      (fun x hx => by rw [inv_inv]; exact ht x hx) hW
  have hne : W ≠ W₂ := by
    intro heq
    have hWt : ∀ w, w ∈ W ↔ t w ∈ W := fun w => by
      have h1 : w ∈ W₂ ↔ t w ∈ W := by rw [hW₂, mem_map_aut_iff, inv_inv]
      rw [← h1, ← heq]
    have hfixt : ∀ w ∈ fixV L, t w ∈ fixV L := fun w hw => mem_fixV_of_conj ht' hw
    have hfixt' : ∀ w ∈ fixV L, t⁻¹ w ∈ fixV L := fun w hw =>
      mem_fixV_of_conj (t := t⁻¹) (fun x hx => by rw [inv_inv]; exact ht x hx) hw
    have hUt : ∀ w, w ∈ W ⊓ fixV L ↔ t w ∈ W ⊓ fixV L := fun w => by
      rw [Subgroup.mem_inf, Subgroup.mem_inf, hWt w]
      refine and_congr_right fun _ => ⟨hfixt w, fun h => ?_⟩
      simpa using hfixt' _ h
    obtain ⟨τ, hτ⟩ := exists_aut_sec hLW hLZ ht hWt hUt
    have hτN := mem_autSec_conj_iff hLW hLZ ht ht' hτ
    obtain ⟨g, hg⟩ := hρx τ hτN
    apply hnot
    refine ⟨g, fun y => ?_⟩
    obtain ⟨l, rfl⟩ := hπ₀ y
    have h1 : thb (π₀ l) = π₀ ⟨t * l * t⁻¹, ht l l.2⟩ := hthb l _ rfl
    rw [h1]
    have hrel : ((ℓ ⟨t * l * t⁻¹, ht l l.2⟩ : ↥(autSec L W (W ⊓ fixV L))) :
        MulAut (Sec W (W ⊓ fixV L))) =
        τ * ((ℓ l : ↥(autSec L W (W ⊓ fixV L))) : MulAut (Sec W (W ⊓ fixV L))) * τ⁻¹ := by
      rw [hℓa hLW hLZ, hℓa hLW hLZ]
      refine MulEquiv.ext fun s => ?_
      simpa [MulAut.mul_apply] using (hτ l (τ⁻¹ s)).symm
    exact hg (ℓ l) (ℓ ⟨t * l * t⁻¹, ht l l.2⟩) hrel
  exact false_of_one_le_rAV hV hA hLq hLA hW hW₂irr hne
    (one_le_rAV_of_qOf hV hA hLq hLA hW hq.ge)

end TripleA6K

end B69K

end CFSG.Quasithin
