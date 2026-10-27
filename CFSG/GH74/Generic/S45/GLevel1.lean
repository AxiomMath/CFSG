module

public import CFSG.GH74.Generic.S45.Struct
public import CFSG.GH74.Generic.S45.Lift
public import CFSG.GH74.Generic.S45.FusionLemmas
public import CFSG.GH74.Generic.Front.Transfer
public import CFSG.GH74.Generic.Lifting

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G]

@[expose] noncomputable def piC (x : G) (g : G) : CentralizerBar x := by
  classical exact if h : g ∈ centralizer ({x} : Set G) then proj x ⟨g, h⟩ else 1

theorem piC_of_mem (x : G) {g : G} (hg : g ∈ centralizer ({x} : Set G)) :
    piC x g = proj x ⟨g, hg⟩ := by
  classical
  simp [piC, hg]

theorem piC_mul (x : G) {a b : G} (ha : a ∈ centralizer ({x} : Set G))
    (hb : b ∈ centralizer ({x} : Set G)) : piC x (a * b) = piC x a * piC x b := by
  rw [piC_of_mem x ha, piC_of_mem x hb, piC_of_mem x (mul_mem ha hb)]
  exact map_mul (proj x) ⟨a, ha⟩ ⟨b, hb⟩

theorem piC_one (x : G) : piC x 1 = 1 := by
  rw [piC_of_mem x (one_mem _)]
  exact map_one (proj x)

theorem piC_inv (x : G) {a : G} (ha : a ∈ centralizer ({x} : Set G)) :
    piC x a⁻¹ = (piC x a)⁻¹ := by
  rw [piC_of_mem x (inv_mem ha), piC_of_mem x ha]
  exact map_inv (proj x) ⟨a, ha⟩

theorem piC_x (x : G) : piC x x = xbar x := by
  rw [piC_of_mem x (mem_centralizer_singleton_iff.2 rfl)]
  rfl

@[expose] def Pre (x : G) (S : Subgroup (CentralizerBar x)) : Subgroup G where
  carrier := {g | g ∈ centralizer ({x} : Set G) ∧ piC x g ∈ S}
  one_mem' := ⟨one_mem _, by rw [piC_one]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨mul_mem ha hb, by rw [piC_mul x ha hb]; exact mul_mem ha' hb'⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨inv_mem ha, by rw [piC_inv x ha]; exact inv_mem ha'⟩

theorem mem_Pre {x : G} {S : Subgroup (CentralizerBar x)} {g : G} :
    g ∈ Pre x S ↔ g ∈ centralizer ({x} : Set G) ∧ piC x g ∈ S := Iff.rfl

structure SylowLift (x : G) (S₀ : Subgroup (CentralizerBar x)) (T : Subgroup G) : Prop where
  sylow : IsSylowOf 2 T (centralizer ({x} : Set G))
  image : ∀ z : CentralizerBar x, z ∈ S₀ ↔ ∃ t ∈ T, piC x t = z

variable [Finite G]

theorem exists_sylowLift (x : G) (S₀ : Sylow 2 (CentralizerBar x)) :
    ∃ T : Subgroup G, SylowLift x (S₀ : Subgroup (CentralizerBar x)) T := by
  obtain ⟨T', hT'⟩ := exists_sylow_map_eq (proj x) (QuotientGroup.mk'_surjective _) S₀
  refine ⟨(T' : Subgroup ↥(centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype,
    ⟨T', rfl⟩, fun z => ?_⟩
  rw [← hT']
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨(h : G), ⟨h, hh, rfl⟩, piC_of_mem x h.2⟩
  · rintro ⟨t, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, hh, (piC_of_mem x h.2).symm⟩

namespace SylowLift

variable {x : G} {S₀ : Subgroup (CentralizerBar x)} {T : Subgroup G}

omit [Finite G] in
theorem le_C (h : SylowLift x S₀ T) : T ≤ centralizer ({x} : Set G) := h.sylow.le

omit [Finite G] in
theorem piC_mem (h : SylowLift x S₀ T) {t : G} (ht : t ∈ T) : piC x t ∈ S₀ :=
  (h.image _).2 ⟨t, ht, rfl⟩

theorem piC_inj (h : SylowLift x S₀ T) {s t : G} (hs : s ∈ T) (ht : t ∈ T)
    (hst : piC x s = piC x t) : s = t := by
  have hsC := h.le_C hs
  have htC := h.le_C ht
  rw [piC_of_mem x hsC, piC_of_mem x htC] at hst
  have hmem : (⟨s, hsC⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * ⟨t, htC⟩ ∈
      pPrimeCore 2 ↥(centralizer ({x} : Set G)) := (QuotientGroup.eq).1 hst
  have hP : IsPGroup 2 ↥(T.subgroupOf (centralizer ({x} : Set G))) :=
    h.sylow.isPGroup.comap_subtype
  have hnT : (⟨s, hsC⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * ⟨t, htC⟩ ∈
      T.subgroupOf (centralizer ({x} : Set G)) := by
    rw [Subgroup.mem_subgroupOf]
    exact mul_mem (inv_mem hs) ht
  have h1 := eq_one_of_isPGroup_of_mem_pPrimeCore hP hnT hmem
  have h2 : s⁻¹ * t = 1 := congrArg Subtype.val h1
  have := congrArg (fun u => s * u) h2
  simpa using this.symm

omit [Finite G] in
theorem x_mem (h : SylowLift x S₀ T) (hx : orderOf x = 2) : x ∈ T := by
  obtain ⟨Q, hQ⟩ := h.sylow
  rw [← hQ]
  exact ⟨xH x, xH_mem_sylow hx Q, rfl⟩

theorem comm (h : SylowLift x S₀ T) (hS : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a) {s t : G}
    (hs : s ∈ T) (ht : t ∈ T) : s * t = t * s := by
  have hsC := h.le_C hs
  have htC := h.le_C ht
  apply h.piC_inj (mul_mem hs ht) (mul_mem ht hs)
  rw [piC_mul x hsC htC, piC_mul x htC hsC]
  exact hS _ (h.piC_mem hs) _ (h.piC_mem ht)

theorem sq_eq_one (h : SylowLift x S₀ T) (hS : ∀ a ∈ S₀, a * a = 1) {t : G} (ht : t ∈ T) :
    t * t = 1 := by
  have htC := h.le_C ht
  apply h.piC_inj (mul_mem ht ht) (one_mem _)
  rw [piC_mul x htC htC, piC_one]
  exact hS _ (h.piC_mem ht)

end SylowLift

theorem exists_nonisolated (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) {x : G}
    (hx : orderOf x = 2) {T : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hxT : x ∈ T) (hab : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) :
    ∃ g : G, g * x * g⁻¹ ∈ T ∧ g * x * g⁻¹ ≠ x := by
  by_contra hcon
  push Not at hcon
  have hTS : IsSylowOf 2 T ⊤ := isSylowOf_top_of_isolated hT hxT hcon
  rw [isSylowOf_iff] at hTS
  obtain ⟨-, hp, hdvd⟩ := hTS
  rw [Subgroup.relIndex_top_right] at hdvd
  let TS : Sylow 2 G := hp.toSylow hdvd
  have hTSeq : (TS : Subgroup G) = T := rfl
  obtain ⟨g, hgT, hgne⟩ := exists_conj_in_sylow_ne hs hn hx TS (by rw [hTSeq]; exact hxT)
    (fun t ht => hab t (by rw [hTSeq] at ht; exact ht) x hxT)
  apply hgne
  have := hcon g⁻¹ (by rw [hTSeq] at hgT; simpa using hgT)
  simpa using this

theorem card_D_eq_two (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) {x : G}
    (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)}
    (hd : KData (CentralizerBar x) K (xbar x)) :
    Nat.card ↥(centralizer (K : Set (CentralizerBar x))) = 2 := by
  by_contra hD2
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨hS2, hSidx⟩ := hd.sup_isSylow' R
  let S₀ : Sylow 2 (CentralizerBar x) := hS2.toSylow hSidx
  have hS₀eq : (S₀ : Subgroup (CentralizerBar x)) =
      (R : Subgroup ↥K).map K.subtype ⊔ centralizer (K : Set (CentralizerBar x)) := rfl
  obtain ⟨T, hT⟩ := exists_sylowLift x S₀
  have hScomm : ∀ a ∈ (S₀ : Subgroup (CentralizerBar x)), ∀ b ∈ (S₀ : Subgroup (CentralizerBar x)),
      a * b = b * a := fun a ha b hb => hd.S_comm R (hS₀eq ▸ ha) (hS₀eq ▸ hb)
  have hxT : x ∈ T := hT.x_mem hx
  have hab : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := fun s hs t ht => hT.comm hScomm hs ht
  obtain ⟨e, heD, hee⟩ := hd.exists_sq_in_D hD2
  have heS : e ∈ (S₀ : Subgroup (CentralizerBar x)) := by
    rw [hS₀eq]; exact mem_sup_right heD
  obtain ⟨t₀, ht₀T, ht₀⟩ := (hT.image e).1 heS
  have ht₀C : t₀ ∈ centralizer ({x} : Set G) := hT.le_C ht₀T
  have ht₀sq : t₀ * t₀ = x := by
    apply hT.piC_inj (mul_mem ht₀T ht₀T) hxT
    rw [piC_mul x ht₀C ht₀C, ht₀, hee, piC_x]
  have hxx : x * x = 1 := by
    rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hR₀K : (R : Subgroup ↥K).map K.subtype ≤ K := Subgroup.map_subtype_le _
  obtain ⟨-, hR₀sq, -⟩ := hd.R_facts R
  have hiso : ∀ g : G, g * x * g⁻¹ ∈ T → g * x * g⁻¹ = x := by
    intro g hg
    obtain ⟨n, hn', hnx⟩ := exists_mem_normalizer_conj_eq hT.sylow hxT hab hg
    have hn'' := Subgroup.mem_normalizer_iff.1 hn'
    have hsT : n * t₀ * n⁻¹ ∈ T := (hn'' t₀).1 ht₀T
    have hsC : n * t₀ * n⁻¹ ∈ centralizer ({x} : Set G) := hT.le_C hsT
    have hyeq : g * x * g⁻¹ = (n * t₀ * n⁻¹) * (n * t₀ * n⁻¹) := by
      rw [← hnx, ← ht₀sq]; group
    have hyT : g * x * g⁻¹ ∈ T := hg
    have hyC : g * x * g⁻¹ ∈ centralizer ({x} : Set G) := hT.le_C hyT
    have hyy : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
      calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hxx]; group
    have hy1 : g * x * g⁻¹ ≠ 1 := by
      intro h1
      have : x = 1 := by
        have := congrArg (fun u => g⁻¹ * u * g) h1
        simpa [mul_assoc] using this
      rw [this, orderOf_one] at hx
      omega
    have hσS : piC x (n * t₀ * n⁻¹) ∈ (S₀ : Subgroup (CentralizerBar x)) := hT.piC_mem hsT
    have hσsq : piC x (n * t₀ * n⁻¹) * piC x (n * t₀ * n⁻¹) = piC x (g * x * g⁻¹) := by
      rw [← piC_mul x hsC hsC, ← hyeq]
    have hne : piC x (n * t₀ * n⁻¹) * piC x (n * t₀ * n⁻¹) ≠ 1 := by
      rw [hσsq]
      intro h1
      apply hy1
      apply hT.piC_inj hyT (one_mem _)
      rw [h1, piC_one]
    have hsq4 : (piC x (n * t₀ * n⁻¹) * piC x (n * t₀ * n⁻¹)) *
        (piC x (n * t₀ * n⁻¹) * piC x (n * t₀ * n⁻¹)) = 1 := by
      rw [hσsq, ← piC_mul x hyC hyC, hyy, piC_one]
    have hz := hd.sq_eq_z hR₀K hR₀sq (hS₀eq ▸ hσS) hne hsq4
    apply hT.piC_inj hyT hxT
    rw [← hσsq, hz, piC_x]
  obtain ⟨g, hg, hne⟩ := exists_nonisolated hs hn hx hT.sylow hxT hab
  exact hne (hiso g hg)

end CFSG.GH74.Generic.S45
