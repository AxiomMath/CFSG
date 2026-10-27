module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrComp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTSub

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem l34g_x_isSL23Mod_comap {C B : Type} [Group C] [Finite C] [Group B] [Finite B]
    {f : C →* B} (hs : Function.Surjective f) (hodd : Odd (Nat.card f.ker)) {K : Subgroup B}
    (hK : IsSL23Mod ↥K) : IsSL23Mod ↥(K.comap f) := by
  let fK : ↥(K.comap f) →* ↥K :=
    (f.comp (K.comap f).subtype).codRestrict K (fun k => Subgroup.mem_comap.mp k.2)
  have hKs : Function.Surjective fK := by
    intro y
    obtain ⟨c, hc⟩ := hs (y : B)
    refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
    rw [Subgroup.mem_comap, hc]
    exact y.2
  have hker : fK.ker = f.ker.comap (K.comap f).subtype := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.mem_ker]
    exact ⟨fun hx => congrArg (fun z : ↥K => (z : B)) hx, fun hx => Subtype.ext hx⟩
  have hKodd : Odd (Nat.card fK.ker) := by
    apply hodd.of_dvd_nat
    rw [hker]
    exact Subgroup.card_comap_dvd_of_injective f.ker (K.comap f).subtype
      (K.comap f).subtype_injective
  obtain ⟨e⟩ := hK
  exact ⟨(sec63PT_oddCoreQuotientEquiv fK hKs hKodd).trans e⟩

private theorem l34g_x_cent_cover {A P : Type} [Group A] [Finite A] [Group P] [Finite P]
    {ψ : A →* P} (h : OddCentralCover ψ) {a : A} (ha : a * a = 1) :
    ∃ g : ↥(Subgroup.centralizer ({a} : Set A)) →* ↥(Subgroup.centralizer ({ψ a} : Set P)),
      (∀ c, (g c : P) = ψ (c : A)) ∧ Function.Surjective g ∧ Odd (Nat.card g.ker) := by
  let C : Subgroup A := Subgroup.centralizer ({a} : Set A)
  let Bbar : Subgroup P := Subgroup.centralizer ({ψ a} : Set P)
  have hmem : ∀ c : ↥C, ψ (c : A) ∈ Bbar := fun c =>
    (SetLike.ext_iff.mp (h.centralizer_singleton_eq_comap ha) (c : A)).mp c.2
  let g : ↥C →* ↥Bbar := (ψ.comp C.subtype).codRestrict Bbar hmem
  have hCmap : C.map ψ = Bbar := h.map_centralizer_singleton ha
  have hsurj : Function.Surjective g := by
    intro y
    have hy : (y : P) ∈ C.map ψ := by rw [hCmap]; exact y.2
    obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨c, hc⟩, Subtype.ext hcq⟩
  have hle : g.ker.map C.subtype ≤ ψ.ker := by
    rintro _ ⟨c, hc, rfl⟩
    exact MonoidHom.mem_ker.mpr
      (congrArg (fun z : ↥Bbar => (z : P)) (MonoidHom.mem_ker.mp hc))
  have hodd : Odd (Nat.card g.ker) := by
    apply h.odd_card_ker.of_dvd_nat
    rw [← Subgroup.card_map_of_injective (K := g.ker) C.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  exact ⟨g, fun c => rfl, hsurj, hodd⟩

theorem l34g_x_isI4PlusIn_top_of_cover {A P : Type} [Group A] [Finite A] [Group P] [Finite P]
    {ψ : A →* P} (h : OddCentralCover ψ) {a : A} (ha : a * a = 1)
    (hP : IsI4PlusIn (⊤ : Subgroup P) (ψ a)) : IsI4PlusIn (⊤ : Subgroup A) a := by
  rw [IsI4PlusIn] at hP ⊢
  have ha_ne : a ≠ 1 := by
    intro h1
    have h2 : orderOf (1 : P) = 2 := by
      rw [← map_one ψ, ← h1]
      exact hP.1
    rw [orderOf_one] at h2
    omega
  have ha2 : orderOf a = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact ha) ha_ne
  refine ⟨ha2, ?_⟩
  obtain ⟨Kbar, hKbar⟩ := hP.2
  obtain ⟨ψC, hψC, hψsurj, hψodd⟩ := l34g_x_cent_cover h ha
  let C : Subgroup A := Subgroup.centralizer ({a} : Set A)
  let Bbar : Subgroup P := Subgroup.centralizer ({ψ a} : Set P)
  let K0 : Subgroup ↥C := (Kbar.subgroupOf Bbar).comap ψC
  have hKbarB : (Kbar.subgroupOf Bbar).IsSubnormal := by
    have h' := hKbar.2.2.1
    rw [show (⊤ ⊓ Bbar) = Bbar from top_inf_eq Bbar] at h'
    exact h'
  have hK0sub : K0.IsSubnormal := Subgroup.IsSubnormal.comap ψC hKbarB
  let K : Subgroup A := K0.map C.subtype
  have haK : a ∈ K := by
    refine Subgroup.mem_map.mpr ⟨⟨a, ?_⟩, ?_, rfl⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · dsimp only [K0]
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hψC]
      exact hKbar.1
  have hKle : K ≤ ⊤ ⊓ Subgroup.centralizer ({a} : Set A) :=
    le_inf le_top (Subgroup.map_subtype_le K0)
  have hKsubC : (K.subgroupOf C).IsSubnormal := by
    have h' : (K0.map C.subtype).subgroupOf C = K0 :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective K0
    rw [show K = K0.map C.subtype from rfl, h']
    exact hK0sub
  have hKsub : (K.subgroupOf (⊤ ⊓ Subgroup.centralizer ({a} : Set A))).IsSubnormal := by
    have htop : (⊤ ⊓ Subgroup.centralizer ({a} : Set A)) = C := top_inf_eq C
    rw [htop]
    exact hKsubC
  have hKbar_le_Bbar : Kbar ≤ Bbar := hKbar.2.1.trans inf_le_right
  have hKbarSubMod : IsSL23Mod ↥(Kbar.subgroupOf Bbar) :=
    isSL23Mod_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKbar_le_Bbar).symm hKbar.2.2.2
  have hK0mod : IsSL23Mod ↥K0 := l34g_x_isSL23Mod_comap hψsurj hψodd hKbarSubMod
  have hKmod : IsSL23Mod ↥K := isSL23Mod_of_mulEquiv
    (Subgroup.equivMapOfInjective K0 C.subtype C.subtype_injective) hK0mod
  exact ⟨K, haK, hKle, hKsub, hKmod⟩

theorem l34g_x_isI4PlusIn_coverDerived {A P : Type} [Group A] [Finite A] [Group P] [Finite P]
    {ρ : A →* P} (h : OddCentralCover ρ) {X : Subgroup P} (hX : CFSG.IsQuasisimple ↥X) {w : A}
    (hw : w * w = 1) (hwX : ρ w ∈ X) (hI : IsI4PlusIn X (ρ w)) :
    IsI4PlusIn (⊤ : Subgroup ↥(coverDerived ρ X))
      (⟨w, h.mem_coverDerived hX hw hwX⟩ : ↥(coverDerived ρ X)) := by
  have haa : (⟨w, h.mem_coverDerived hX hw hwX⟩ : ↥(coverDerived ρ X)) *
      ⟨w, h.mem_coverDerived hX hw hwX⟩ = 1 := Subtype.ext hw
  have hhom : coverDerivedHom ρ X ⟨w, h.mem_coverDerived hX hw hwX⟩ =
      (⟨ρ w, hwX⟩ : ↥X) := Subtype.ext rfl
  have hI' : IsI4PlusIn (⊤ : Subgroup ↥X) (⟨ρ w, hwX⟩ : ↥X) :=
    l34g_isI4PlusIn_top_of_subtype hwX hI
  exact l34g_x_isI4PlusIn_top_of_cover (A := ↥(coverDerived ρ X)) (P := ↥X)
    (h.oddCentralCover_coverDerivedHom hX) haa (by rw [hhom]; exact hI')

theorem l34g_x_isI4PlusIn_map_inj {X : Type} [Group X] (f : X →* G) (hf : Function.Injective f)
    {J₀ : Subgroup X} {w : X} (hw : w ∈ J₀)
    (h : IsI4PlusIn (⊤ : Subgroup ↥J₀) (⟨w, hw⟩ : ↥J₀)) : IsI4PlusIn (J₀.map f) (f w) := by
  let e : ↥J₀ ≃* ↥(J₀.map f) := J₀.equivMapOfInjective f hf
  have h1 : IsI4PlusIn (⊤ : Subgroup ↥(J₀.map f)) (e ⟨w, hw⟩) :=
    isI4PlusIn_top_map_mulEquiv e h
  have he : e ⟨w, hw⟩ = (⟨f w, Subgroup.mem_map_of_mem f hw⟩ : ↥(J₀.map f)) :=
    Subtype.ext rfl
  rw [he] at h1
  exact isI4PlusIn_of_top (Subgroup.mem_map_of_mem f hw) h1

end CFSG.OddStandard.SmallF3.Omega
