module

public import CFSG.ClassicalInvolution.AschTight.Sec7L612B
public import CFSG.ClassicalInvolution.AschTight.Sec7L76C
public import CFSG.ClassicalInvolution.AschTight.S1911C8a
public import CFSG.ClassicalInvolution.AschTight.S1916Sec

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

theorem forall_conjSub_inv_mem {η : Set (Subgroup G)} {m : G}
    (hm : ∀ U ∈ η, conjSub m U ∈ η) : ∀ U ∈ η, conjSub m⁻¹ U ∈ η := by
  let φ : ↥η → ↥η := fun U => ⟨conjSub m U, hm U U.2⟩
  have hinj : Function.Injective φ := fun U₁ U₂ h =>
    Subtype.ext (conjSub_injective m (congrArg Subtype.val h))
  have : Finite ↥η := Set.toFinite η
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro U hU
  obtain ⟨U', hU'⟩ := hsurj ⟨U, hU⟩
  have e : conjSub m (U' : Subgroup G) = U := congrArg Subtype.val hU'
  rw [← e, conjSub_inv_conjSub]
  exact U'.2

@[expose] def permSub (η : Set (Subgroup G)) : Subgroup G where
  carrier := {m | ∀ U ∈ η, conjSub m U ∈ η}
  one_mem' := fun U hU => by rwa [conjSub_one]
  mul_mem' := fun ha hb U hU => by
    rw [conjSub_mul]
    exact ha _ (hb U hU)
  inv_mem' := fun hm => forall_conjSub_inv_mem hm

theorem mem_permSub_iff {η : Set (Subgroup G)} {m : G} :
    m ∈ permSub η ↔ ∀ U ∈ η, conjSub m U ∈ η :=
  Iff.rfl

variable {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem forall_conjSub_mem_of_mem_iSup (hd : Sec19DataT p f K z S W L t V)
    {η : Set (Subgroup G)} (hη : η ∈ etaG (CoreAssembly.conjClass K))
    (hηS : ∀ U ∈ η, U ≤ (S : Subgroup G)) {m : G}
    (hm : m ∈ ⨆ U ∈ {U : Subgroup G | (∃ η' ∈ etaG (CoreAssembly.conjClass K), U ∈ η') ∧
      U ≤ (S : Subgroup G)}, U) :
    ∀ U ∈ η, conjSub m U ∈ η := by
  have ht := hd.tight
  have h610 := (l6_10_proved p f ht.branch.odd ht.branch.five G _ (hypOmegaMod_of_tightD ht) S
    η hη hηS).2
  refine mem_permSub_iff.mp ((iSup₂_le fun U hU => ?_ : _ ≤ permSub η) hm)
  obtain ⟨⟨η', ⟨S', hη'S', -⟩, hUη'⟩, hUS⟩ := hU
  have hUU : U ∈ USet (CoreAssembly.conjClass K) := (hη'S'.1 hUη').1
  exact fun u hu => mem_permSub_iff.mpr (h610 U hUU hUS u hu)

theorem weaklyClosedIn_W (hd : Sec19DataT p f K z S W L t V) :
    Sec7.WeaklyClosedIn W (S : Subgroup G) := by
  have hd0 := hd.toSec19Data
  have ht := hd.tight
  have hp := ht.branch.odd
  have hq := ht.branch.five
  have hΩ := hypOmegaMod_of_tightD ht
  obtain ⟨η, hη, hWη⟩ := hd.hW
  have hηS : ∀ U ∈ η, U ≤ (S : Subgroup G) := fun U hU =>
    (hWη ▸ le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) U hU le_rfl).trans hd.hWS
  have htr : ∀ K₁ ∈ CoreAssembly.conjClass K, ∀ K₂ ∈ CoreAssembly.conjClass K,
      ∃ g : G, conjSub g K₁ = K₂ := by
    rintro K₁ ⟨g₁, rfl⟩ K₂ ⟨g₂, rfl⟩
    exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have h612 := Sec7.l6_12_on hp hq hΩ (fun S => (l6_9_proved p f hp hq G _ hΩ S).1)
    (fun η ⟨S, hS, hinv⟩ => ((l6_9_proved p f hp hq G _ hΩ S).2 η hS hinv).1)
    (l6_11_proved p f hp hq G _ hΩ) htr S
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | h2
  · have heq : η = η₀ := huniq η hη fun m hm U hU =>
      forall_conjSub_mem_of_mem_iSup hd hη hηS hm U hU
    subst heq
    intro g hg
    rw [hWη] at hg ⊢
    refine Sec7.conjSub_iSup_eq_of_forall_mem (hwc g fun U hU => ?_)
    exact (conjSub_mono (le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) U hU le_rfl)).trans hg
  · exfalso
    have hV4 := S1911.four_le_card hd
    have hLS : L ⊓ (S : Subgroup G) = V := by rw [inf_comm]; exact S1911.inf_member_eq hd
    obtain ⟨M, hM, hVM⟩ := exists_isSylow2In_of_mem_RSet (hLS ▸ h2 L hd.memL (by rw [hLS]; omega))
    have h1 := hΩ.natCard_isSylow2In hM hVM
    rw [← hΩ.natCard_isSylow2In (CoreAssembly.mem_conjClass_self K)
      (S1916.sd_isSylow2In_R hd0), S1911.card_inf_eq hd0, S1911.card_inf_eq_card hd] at h1
    omega

theorem le_normalizer_W (hd : Sec19DataT p f K z S W L t V) :
    (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  intro s hs
  refine mem_normalizer_iff_conjSub_eq.mpr (weaklyClosedIn_W hd s ?_)
  refine (conjSub_mono hd.hWS).trans fun x hx => ?_
  rw [mem_conjSub_iff] at hx
  have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
  rw [e]
  exact (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hx) ((S : Subgroup G).inv_mem hs)

theorem exists_normalizer_conj_eq (hd : Sec19DataT p f K z S W L t V) {x g : G}
    (hx : x ∈ Subgroup.centralizer (W : Set G))
    (hgx : g * x * g⁻¹ ∈ Subgroup.centralizer (W : Set G)) :
    ∃ n ∈ Subgroup.normalizer (W : Set G), n * x * n⁻¹ = g * x * g⁻¹ :=
  Sec7.control_centralizer_of_weaklyClosed (S.isPGroup'.to_le hd.hWS) (weaklyClosedIn_W hd) hx
    hgx

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19B
