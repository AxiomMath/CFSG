module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

open Classical in
noncomputable def act (p : ℕ) (K : Subgroup G) (g : G) : MulAut (PSimple p K) :=
  if h : g ∈ Subgroup.normalizer (K : Set G) then chevAut p K ⟨g, h⟩ else 1

theorem act_of_mem {p : ℕ} {K : Subgroup G} {g : G} (h : g ∈ Subgroup.normalizer (K : Set G)) :
    act p K g = chevAut p K ⟨g, h⟩ :=
  dif_pos h

theorem act_mul {p : ℕ} {K : Subgroup G} {g h : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hh : h ∈ Subgroup.normalizer (K : Set G)) : act p K (g * h) = act p K g * act p K h := by
  rw [act_of_mem hg, act_of_mem hh, act_of_mem (Subgroup.mul_mem _ hg hh), ← map_mul]
  rfl

theorem act_eq_one_iff {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K)
    {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    act p K g = 1 ↔ CentMod p K g := by
  rw [act_of_mem hg]
  exact chevAut_eq_one_iff hp hK hg

theorem act_of_mem_K {p : ℕ} {K : Subgroup G} {k : G} (hk : k ∈ K) :
    act p K k = MulAut.conj (chevQuotHom p K ⟨k, hk⟩) := by
  rw [act_of_mem (Subgroup.le_normalizer hk)]
  ext t
  obtain ⟨s, rfl⟩ := chevQuotHom_surjective p K t
  rw [chevAut_chevQuotHom, MulAut.conj_apply]
  have h : K.normalizerMonoidHom ⟨k, Subgroup.le_normalizer hk⟩ s = ⟨k, hk⟩ * s * ⟨k, hk⟩⁻¹ :=
    Subtype.ext rfl
  rw [h, map_mul, map_mul, map_inv]

noncomputable def actImage (p : ℕ) (K S : Subgroup G) : Subgroup (MulAut (PSimple p K)) :=
  (S.subgroupOf (Subgroup.normalizer (K : Set G))).map (chevAut p K)

theorem mem_actImage_iff {p : ℕ} {K S : Subgroup G} (hS : S ≤ Subgroup.normalizer (K : Set G))
    {t : MulAut (PSimple p K)} : t ∈ actImage p K S ↔ ∃ g ∈ S, act p K g = t := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, Subgroup.mem_subgroupOf.1 hg, act_of_mem g.2⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hS hg⟩, Subgroup.mem_subgroupOf.2 hg, (act_of_mem (hS hg)).symm⟩

theorem actImage_mono {p : ℕ} {K S T : Subgroup G} (h : S ≤ T) :
    actImage p K S ≤ actImage p K T :=
  Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem isSubnormal_actImage {p : ℕ} {K J C : Subgroup G} (hJC : IsSubnormal J C) :
    IsSubnormal (actImage p K J) (actImage p K C) :=
  isSubnormal_map' (chevAut p K) (isSubnormal_comap' (Subgroup.normalizer (K : Set G)).subtype hJC)

theorem act_mem_range {p : ℕ} {K : Subgroup G} {k : G} (hk : k ∈ K) :
    act p K k ∈ (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range :=
  ⟨chevQuotHom p K ⟨k, hk⟩, (act_of_mem_K hk).symm⟩

theorem actImage_K_eq_range {p : ℕ} {K : Subgroup G} :
    actImage p K K = (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range := by
  ext t
  rw [mem_actImage_iff Subgroup.le_normalizer]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact act_mem_range hg
  · rintro ⟨s, rfl⟩
    obtain ⟨k, rfl⟩ := chevQuotHom_surjective p K s
    exact ⟨k, k.2, act_of_mem_K k.2⟩

theorem conj_injective {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K) :
    Function.Injective (MulAut.conj : PSimple p K →* MulAut (PSimple p K)) := by
  obtain ⟨hs, hna⟩ := chev_pSimple_simple_nonabelian hp hK
  haveI := hs
  have hz : Subgroup.center (PSimple p K) = ⊥ := chev_center_eq_bot_of_simple_nonabelian hna
  intro s t hst
  have hzc : t * s⁻¹ ∈ Subgroup.center (PSimple p K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := DFunLike.congr_fun hst (s⁻¹ * x * s)
    simp only [MulAut.conj_apply] at h1
    calc x * (t * s⁻¹) = (t * (s⁻¹ * x * s) * t⁻¹) * (t * s⁻¹) := by
          rw [← h1]; group
      _ = (t * s⁻¹) * x := by group
  rw [hz, Subgroup.mem_bot, mul_inv_eq_one] at hzc
  exact hzc.symm

theorem isSimpleGroup_range {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (hK : GLAPComponent p X K) :
    IsSimpleGroup ↥(MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range := by
  obtain ⟨hs, -⟩ := chev_pSimple_simple_nonabelian hp hK
  exact (MulEquiv.isSimpleGroup_congr (MonoidHom.ofInjective (conj_injective hp hK))).1 hs

theorem eq_bot_or_eq_of_isSubnormal_simple {M : Type*} [Group M] (R : Subgroup M) [IsSimpleGroup R]
    {A B : Subgroup M} (h : IsSubnormal A B) : B = R → A = ⊥ ∨ A = R := by
  induction h with
  | refl H => exact fun hH => Or.inr hH
  | @step H M' K hHM hn _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · left
      exact le_bot_iff.1 (hM ▸ hHM)
    · subst hM
      haveI : (H.subgroupOf M').Normal := hn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf M') with h1 | h1
      · left
        ext y
        constructor
        · intro hy
          have hmem : (⟨y, hHM hy⟩ : ↥M') ∈ H.subgroupOf M' := Subgroup.mem_subgroupOf.2 hy
          rw [h1, Subgroup.mem_bot] at hmem
          exact congrArg Subtype.val hmem
        · intro hy
          rw [Subgroup.mem_bot] at hy
          subst hy
          exact H.one_mem
      · right
        apply le_antisymm hHM
        intro r hr
        have hmem : (⟨r, hr⟩ : ↥M') ∈ H.subgroupOf M' := by
          rw [h1]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.1 hmem

theorem not_coprime_card_psimple {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (hK : GLAPComponent p X K) : ¬ Nat.Coprime p (Nat.card (PSimple p K)) := by
  intro hcop
  haveI : Fact p.Prime := ⟨hp⟩
  have htop : (⊤ : Subgroup (PSimple p K)) ≤ GLAPPrimeCore p (PSimple p K) :=
    le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
  rw [glaPPrimeCore_pSimple_eq_bot hp hK, le_bot_iff] at htop
  obtain ⟨hs, _⟩ := chev_pSimple_simple_nonabelian hp hK
  haveI := hs.toNontrivial
  exact ((Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup (PSimple p K))).1 inferInstance) htop

theorem conj_mem_centMod' {p : ℕ} {L : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hc : c ∈ centModSubgroup p L) :
    g * c * g⁻¹ ∈ centModSubgroup p L := by
  obtain ⟨hcN, hcJ⟩ := hc
  refine ⟨?_, fun l hl => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcN) (Subgroup.inv_mem _ hg)
  · have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) l).1 hl
      simpa using this
    have h1 := hcJ _ hl'
    have h2 : g * ⁅g⁻¹ * l * g, c⁆ * g⁻¹ ∈ GLAPPrimeCoreOf p L :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p L hg) _).1 h1
    have h3 : ⁅l, g * c * g⁻¹⁆ = g * ⁅g⁻¹ * l * g, c⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h3]; exact h2

theorem normalizer_le_normalizer_centMod' (p : ℕ) (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (centModSubgroup p L : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_centMod' hb hy, fun hy => ?_⟩
  have := conj_mem_centMod' (Subgroup.inv_mem _ hb) hy
  simpa [mul_assoc] using this

theorem mem_sup_centMod {p : ℕ} {L : Subgroup G} {x : G} (hx : x ∈ L ⊔ centModSubgroup p L) :
    ∃ l ∈ L, ∃ n ∈ centModSubgroup p L, x = l * n := by
  have h : L ≤ Subgroup.normalizer (centModSubgroup p L : Set G) := fun l hl =>
    normalizer_le_normalizer_centMod' p L (Subgroup.le_normalizer hl)
  have hx' : x ∈ ((L ⊔ centModSubgroup p L : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L _ h] at hx'
  obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, n, hn, rfl⟩

theorem mem_sup_centMod' {p : ℕ} {L A : Subgroup G} (hA : A ≤ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ A ⊔ centModSubgroup p L) :
    ∃ a ∈ A, ∃ n ∈ centModSubgroup p L, x = a * n := by
  have hA' : A ≤ Subgroup.normalizer (centModSubgroup p L : Set G) :=
    hA.trans (normalizer_le_normalizer_centMod' p L)
  have hx' : x ∈ ((A ⊔ centModSubgroup p L : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A _ hA'] at hx'
  obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨a, ha, n, hn, rfl⟩

theorem act_eq_one_of_centMod {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K)
    {m : G} (hm : m ∈ centModSubgroup p K) : act p K m = 1 :=
  (act_eq_one_iff hp hK hm.1).2 (centMod_iff.2 hm)

theorem actImage_le_range {p : ℕ} (hp : p.Prime) {X K S : Subgroup G} (hK : GLAPComponent p X K)
    (hS : S ≤ K ⊔ centModSubgroup p K) :
    actImage p K S ≤ (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range := by
  intro t ht
  have hSN : S ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    (sup_le Subgroup.le_normalizer fun m hm => (mem_centModSubgroup.1 hm).1) (hS hg)
  obtain ⟨g, hg, rfl⟩ := (mem_actImage_iff hSN).1 ht
  obtain ⟨k, hk, m, hm, rfl⟩ := mem_sup_centMod (hS hg)
  rw [act_mul (Subgroup.le_normalizer hk) (mem_centModSubgroup.1 hm).1,
    act_eq_one_of_centMod hp hK hm, mul_one]
  exact act_mem_range hk

theorem actImage_sup_eq_range {p : ℕ} (hp : p.Prime) {X K S : Subgroup G}
    (hK : GLAPComponent p X K) (hKS : K ≤ S) (hS : S ≤ K ⊔ centModSubgroup p K) :
    actImage p K S = (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range :=
  le_antisymm (actImage_le_range hp hK hS) (by
    rw [← actImage_K_eq_range]
    exact actImage_mono hKS)

theorem act_core_eq_one {x : G} {p : ℕ} (hp : p.Prime) (hx : x ^ p = 1)
    {X K : Subgroup G} (hxX : x ∈ X) (hK : GLAPComponent p X K)
    (hxK : x ∉ Subgroup.normalizer (K : Set G)) {n : G}
    (hn : n ∈ GLAPPrimeCoreOf p (closureIn K (Subgroup.zpowers x))) :
    act p K n = 1 := by
  set Ks := closureIn K (Subgroup.zpowers x) with hKs
  have hKsS : Ks ≤ K ⊔ centModSubgroup p K := closureIn_le_sup_centMod hp hx hxX hK hxK
  have hKsN : Ks ≤ Subgroup.normalizer (K : Set G) := closureIn_le_normalizer hp hx hxX hK hxK
  have hNKs : GLAPPrimeCoreOf p Ks ≤ Ks := Subgroup.map_subtype_le _
  have hnorm : (GLAPPrimeCoreOf p Ks).subgroupOf Ks |>.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNKs).2
      (le_normalizer_glaPPrimeCoreOf p Ks)
  have hsub : IsSubnormal (GLAPPrimeCoreOf p Ks) Ks :=
    IsSubnormal.step hNKs hnorm (IsSubnormal.refl Ks)
  have hsn := isSubnormal_actImage (p := p) (K := K) hsub
  have hKs_img : actImage p K Ks = (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range :=
    actImage_sup_eq_range hp hK (le_closureIn_self K _) hKsS
  rw [hKs_img] at hsn
  have hNN : GLAPPrimeCoreOf p Ks ≤ Subgroup.normalizer (K : Set G) := hNKs.trans hKsN
  have himg : actImage p K (GLAPPrimeCoreOf p Ks) = ⊥ := by
    haveI := isSimpleGroup_range hp hK
    rcases eq_bot_or_eq_of_isSubnormal_simple
      (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range hsn rfl with h | h
    · exact h
    · exfalso
      have e : Nat.card ↥(GLAPPrimeCoreOf p Ks) =
          Nat.card ↥((GLAPPrimeCoreOf p Ks).subgroupOf (Subgroup.normalizer (K : Set G))) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNN).toEquiv).symm
      have hdvd : Nat.card ↥(actImage p K (GLAPPrimeCoreOf p Ks)) ∣
          Nat.card ↥(GLAPPrimeCoreOf p Ks) := by
        rw [e]
        exact Subgroup.card_map_dvd _ _
      rw [h] at hdvd
      have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p Ks)) :=
        (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp Ks)
      have hR : Nat.card ↥(MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range =
          Nat.card (PSimple p K) :=
        Nat.card_congr (MonoidHom.ofInjective (conj_injective hp hK)).toEquiv.symm
      rw [hR] at hdvd
      exact not_coprime_card_psimple hp hK (Nat.Coprime.coprime_dvd_right hdvd hcop)
  have hmem : act p K n ∈ actImage p K (GLAPPrimeCoreOf p Ks) :=
    (mem_actImage_iff hNN).2 ⟨n, hn, rfl⟩
  rw [himg, Subgroup.mem_bot] at hmem
  exact hmem

end CFSG.LocalAnalysis.GLTheoremA.I155X
