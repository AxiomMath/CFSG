module

public import CFSG.Goldschmidt75.Transfer
public import CFSG.Goldschmidt75.TheoremBa
public import CFSG.Goldschmidt75.TheoremBcN1
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped Pointwise commutatorElement

universe u

section HSet

variable {G : Type*} [Group G]

@[expose] def hSet (S K E : Subgroup G) [E.Normal] : Subgroup G :=
  K ⊓ (centralizer ((S.map (QuotientGroup.mk' E) : Subgroup (G ⧸ E)) : Set (G ⧸ E))).comap
    (QuotientGroup.mk' E)

theorem mem_hSet {S K E : Subgroup G} [E.Normal] {g : G} :
    g ∈ hSet S K E ↔ g ∈ K ∧ QuotientGroup.mk' E g ∈
      centralizer ((S.map (QuotientGroup.mk' E) : Subgroup (G ⧸ E)) : Set (G ⧸ E)) :=
  Iff.rfl

theorem hSet_le (S K E : Subgroup G) [E.Normal] : hSet S K E ≤ K := inf_le_left

theorem commutator_le_of_hSet (S K E : Subgroup G) [E.Normal] : ⁅S, hSet S K E⁆ ≤ E := by
  rw [commutator_le]
  intro s hs h hh
  have h1 : QuotientGroup.mk' E ⁅s, h⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mem_centralizer_iff.mp (mem_hSet.1 hh).2 _ ⟨s, hs, rfl⟩
  rwa [← QuotientGroup.ker_mk' E, MonoidHom.mem_ker]

theorem mem_hSet_of_mem_normalizer {S K E : Subgroup G} [E.Normal] [K.Normal]
    (hE : S ⊓ K ≤ E) {g : G} (hgK : g ∈ K) (hgS : g ∈ normalizer (S : Set G)) :
    g ∈ hSet S K E := by
  refine mem_hSet.2 ⟨hgK, ?_⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨s, hs, rfl⟩
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_eq_mk']
  refine ⟨(s * g)⁻¹ * (g * s), hE ⟨?_, ?_⟩, by group⟩
  · have h1 : g⁻¹ * s⁻¹ * g ∈ S := by
      have := (mem_normalizer_iff.mp ((normalizer _).inv_mem hgS) s⁻¹).mp (S.inv_mem hs)
      simpa using this
    have := S.mul_mem h1 hs
    rw [show (s * g)⁻¹ * (g * s) = g⁻¹ * s⁻¹ * g * s by group]
    exact this
  · rw [show (s * g)⁻¹ * (g * s) = g⁻¹ * (s⁻¹ * g * s) by group]
    have h2 : s⁻¹ * g * s ∈ K := by
      have := (inferInstance : K.Normal).conj_mem _ hgK s⁻¹
      simpa using this
    exact K.mul_mem (K.inv_mem hgK) h2

end HSet

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem focal_generator_mem (P : Sylow p G) {S S₀ : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) [S₀.Normal]
    [(S ⊓ centralizer (S₀ : Set G)).Normal] (hES₀ : S ⊓ centralizer (S₀ : Set G) ≤ S₀)
    {q u : G} (hq : q ∈ (P : Subgroup G) ⊓ centralizer (S₀ : Set G))
    (hu : u ∈ centralizer (S₀ : Set G))
    (hc : ⁅q, u⁆ ∈ (P : Subgroup G) ⊓ centralizer (S₀ : Set G)) :
    ⁅q, u⁆ ∈ ⁅hSet S (centralizer (S₀ : Set G)) (S ⊓ centralizer (S₀ : Set G)),
      hSet S (centralizer (S₀ : Set G)) (S ⊓ centralizer (S₀ : Set G))⁆ := by
  set K := centralizer (S₀ : Set G)
  set E := S ⊓ K
  set H := hSet S K E
  set Q := (P : Subgroup G) ⊓ K
  have hKn : K.Normal := inferInstance
  have hEK : ∀ e ∈ E, ∀ k ∈ K, e * k = k * e := fun e he k hk =>
    mem_centralizer_iff.mp hk e (hES₀ he)
  have hQH : Q ≤ H := fun x hx =>
    mem_hSet_of_mem_normalizer le_rfl hx.2 (sylow_le_normalizer P hSP hS hx.1)
  set y₀ := u * q * u⁻¹
  have hy₀ : y₀ ∈ Q := by
    have h1 : y₀⁻¹ = q⁻¹ * ⁅q, u⁆ := by simp only [y₀, commutatorElement_def]; group
    have h2 : y₀⁻¹ ∈ Q := h1 ▸ Q.mul_mem (Q.inv_mem hq) hc
    simpa using Q.inv_mem h2
  set K₁ := S ⊔ K
  have hKK₁ : K ≤ K₁ := le_sup_right
  have hSK₁ : S ≤ K₁ := le_sup_left
  obtain ⟨T₁, hT₁⟩ :=
    ((P.isPGroup'.to_inf_left (K := K₁)).comap_subtype (K := K₁)).exists_le_sylow
  have hST : S.subgroupOf K₁ ≤ T₁ := fun y hy =>
    hT₁ (show (y : G) ∈ (P : Subgroup G) ⊓ K₁ from ⟨hSP hy, y.2⟩)
  have hSc := stronglyClosed_subgroupOf P hS hSK₁ T₁ hST
  set q' : K₁ := ⟨q, hKK₁ hq.2⟩
  set u' : K₁ := ⟨u, hKK₁ hu⟩
  have hq'T : ({q'} : Set K₁) ⊆ T₁ := Set.singleton_subset_iff.mpr
    (hT₁ (show (q : G) ∈ (P : Subgroup G) ⊓ K₁ from ⟨hq.1, hKK₁ hq.2⟩))
  have hconj : rconj u'⁻¹ ({q'} : Set K₁) = {u' * q' * u'⁻¹} := by
    ext z
    simp only [mem_rconj, inv_inv, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← h]; group
    · intro h; rw [h]; group
  have hy₀T : rconj u'⁻¹ ({q'} : Set K₁) ⊆ T₁ := by
    rw [hconj]
    exact Set.singleton_subset_iff.mpr (hT₁ (show ((u' * q' * u'⁻¹ : K₁) : G) ∈
      (P : Subgroup G) ⊓ K₁ from ⟨hy₀.1, (u' * q' * u'⁻¹).2⟩))
  obtain ⟨n', hn', heq⟩ := baFor p K₁ T₁ (S.subgroupOf K₁) hST hSc {q'} hq'T u'⁻¹ hy₀T
  rw [hconj] at heq
  have hmem : n'⁻¹ * q' * n' ∈
      ((S.subgroupOf K₁ : Subgroup K₁) : Set K₁) * {u' * q' * u'⁻¹} := by
    rw [← heq]
    exact conj_mem_rconj ⟨1, (S.subgroupOf K₁).one_mem, q', rfl, one_mul q'⟩
  obtain ⟨s', hs', _, rfl, hseq⟩ := hmem
  have hn : (n' : G) ∈ normalizer (S : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf hSK₁ hn'
  have hsS : (s' : G) ∈ S := hs'
  have hseqG : (s' : G) * y₀ = (n' : G)⁻¹ * q * n' := by
    have := congrArg Subtype.val hseq
    simpa [y₀, q', u', mul_assoc] using this
  obtain ⟨c₁, hc₁, s₁, hs₁, hcs⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (show (n' : G) ∈ K ⊔ S from sup_comm S K ▸ n'.2)
  have hc₁N : c₁ ∈ normalizer (S : Set G) := by
    have e : c₁ = (n' : G) * s₁⁻¹ := by rw [← hcs]; group
    rw [e]
    exact (normalizer _).mul_mem hn ((normalizer _).inv_mem (Subgroup.le_normalizer hs₁))
  have hc₁H : c₁ ∈ H := mem_hSet_of_mem_normalizer le_rfl hc₁ hc₁N
  set q₁ := c₁⁻¹ * q * c₁
  have hq₁K : q₁ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hc₁) hq.2) hc₁
  have hq₁N : q₁ ∈ normalizer (S : Set G) :=
    (normalizer _).mul_mem ((normalizer _).mul_mem ((normalizer _).inv_mem hc₁N)
      (sylow_le_normalizer P hSP hS hq.1)) hc₁N
  set e₁ := q₁⁻¹ * s₁⁻¹ * q₁ * s₁
  have he₁ : e₁ ∈ E := by
    refine ⟨?_, ?_⟩
    · have h1 : q₁⁻¹ * s₁⁻¹ * q₁ ∈ S := by
        have := (mem_normalizer_iff.mp ((normalizer _).inv_mem hq₁N) s₁⁻¹).mp (S.inv_mem hs₁)
        simpa using this
      exact S.mul_mem h1 hs₁
    · have h2 : s₁⁻¹ * q₁ * s₁ ∈ K := by
        have := hKn.conj_mem _ hq₁K s₁⁻¹
        simpa using this
      rw [show e₁ = q₁⁻¹ * (s₁⁻¹ * q₁ * s₁) by simp only [e₁]; group]
      exact K.mul_mem (K.inv_mem hq₁K) h2
  have hnq : (n' : G)⁻¹ * q * n' = q₁ * e₁ := by
    rw [← hcs]; simp only [q₁, e₁]; group
  have hsK : (s' : G) ∈ K := by
    have e : (s' : G) = q₁ * e₁ * y₀⁻¹ := by
      rw [← hnq, ← hseqG]; group
    rw [e]
    exact K.mul_mem (K.mul_mem hq₁K he₁.2) (K.inv_mem hy₀.2)
  have hsE : (s' : G) ∈ E := ⟨hsS, hsK⟩
  set e := e₁⁻¹ * s'
  have heE : e ∈ E := E.mul_mem (E.inv_mem he₁) hsE
  have hy₀' : y₀ = (s' : G)⁻¹ * (q₁ * e₁) := by rw [← hnq, ← hseqG]; group
  have hcomm : e₁⁻¹ * q₁⁻¹ = q₁⁻¹ * e₁⁻¹ := hEK _ (E.inv_mem he₁) _ (K.inv_mem hq₁K)
  have hdec : ⁅q, u⁆ = ⁅q, c₁⁻¹⁆ * e := by
    have hqu : ⁅q, u⁆ = q * y₀⁻¹ := by simp only [y₀, commutatorElement_def]; group
    have hqc : ⁅q, c₁⁻¹⁆ = q * q₁⁻¹ := by simp only [q₁, commutatorElement_def]; group
    rw [hqu, hy₀', hqc]
    calc q * ((s' : G)⁻¹ * (q₁ * e₁))⁻¹ = q * ((e₁⁻¹ * q₁⁻¹) * s') := by group
      _ = q * ((q₁⁻¹ * e₁⁻¹) * s') := by rw [hcomm]
      _ = q * q₁⁻¹ * e := by simp only [e]; group
  have hc₁q : ⁅q, c₁⁻¹⁆ ∈ ⁅H, H⁆ := commutator_mem_commutator (hQH hq) (H.inv_mem hc₁H)
  have heK : e ∈ ⁅K, K⁆ := by
    have e2 : e = ⁅q, c₁⁻¹⁆⁻¹ * ⁅q, u⁆ := by rw [hdec]; group
    rw [e2]
    exact ⁅K, K⁆.mul_mem (⁅K, K⁆.inv_mem (commutator_mem_commutator hq.2 (K.inv_mem hc₁)))
      (commutator_mem_commutator hq.2 hu)
  obtain ⟨QK, hQK⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hQKmap : (QK : Subgroup K).map K.subtype = Q := by
    rw [hQK, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  set e' : K := ⟨e, heE.2⟩
  have he'c : e' ∈ center K := mem_center_iff.mpr fun k => Subtype.ext (hEK e heE k k.2).symm
  have he'Q : e' ∈ (QK : Subgroup K) := by
    rw [hQK]; exact ⟨hSP heE.1, heE.2⟩
  have he'K : e' ∈ commutator K := by
    rw [← Subgroup.map_subtype_commutator] at heK
    obtain ⟨w, hw, hwe⟩ := heK
    have : w = e' := Subtype.ext hwe
    rwa [← this]
  have he'QQ := mem_commutator_of_mem_center QK he'c he'Q he'K
  have heQQ : e ∈ ⁅Q, Q⁆ := by
    rw [← hQKmap, ← Subgroup.map_commutator]
    exact ⟨e', he'QQ, rfl⟩
  rw [hdec]
  exact ⁅H, H⁆.mul_mem hc₁q (Subgroup.commutator_mono hQH hQH heQQ)

theorem commutator_inf_le_hSet (P : Sylow p G) {S S₀ : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) [S₀.Normal]
    [(S ⊓ centralizer (S₀ : Set G)).Normal] (hES₀ : S ⊓ centralizer (S₀ : Set G) ≤ S₀) :
    ⁅centralizer (S₀ : Set G), centralizer (S₀ : Set G)⁆ ⊓
        ((P : Subgroup G) ⊓ centralizer (S₀ : Set G)) ≤
      ⁅hSet S (centralizer (S₀ : Set G)) (S ⊓ centralizer (S₀ : Set G)),
        hSet S (centralizer (S₀ : Set G)) (S ⊓ centralizer (S₀ : Set G))⁆ := by
  set K := centralizer (S₀ : Set G)
  rintro y ⟨hyKK, hyQ⟩
  obtain ⟨QK, hQK⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hyK : y ∈ K := hyQ.2
  have hy' : (⟨y, hyK⟩ : K) ∈ commutator K ⊓ (QK : Subgroup K) := by
    refine ⟨?_, by rw [hQK]; exact hyQ⟩
    rw [← Subgroup.map_subtype_commutator] at hyKK
    obtain ⟨w, hw, hwe⟩ := hyKK
    have : w = ⟨y, hyK⟩ := Subtype.ext hwe
    rwa [← this]
  rw [Subgroup.commutator_inf_eq_focalSubgroup QK, Subgroup.focalSubgroup_def] at hy'
  suffices hle : closure {g : K | g ∈ (QK : Subgroup K) ∧
      ∃ x ∈ (QK : Subgroup K), ∃ u : K, g = ⁅x, u⁆} ≤
      (⁅hSet S K (S ⊓ K), hSet S K (S ⊓ K)⁆).comap K.subtype from hle hy'
  rw [closure_le]
  rintro g ⟨hg, x, hx, u, rfl⟩
  rw [hQK] at hg hx
  have hcoe : ((⁅x, u⁆ : K) : G) = ⁅(x : G), (u : G)⁆ := by
    simp [commutatorElement_def]
  have hg' : ⁅(x : G), (u : G)⁆ ∈ (P : Subgroup G) ⊓ K := by
    rw [← hcoe]; exact hg
  show ((⁅x, u⁆ : K) : G) ∈ ⁅hSet S K (S ⊓ K), hSet S K (S ⊓ K)⁆
  rw [hcoe]
  exact focal_generator_mem P hSP hS hES₀ hx u.2 hg'

theorem rcSet_stronglyClosed_of_normal_inf (P : Sylow p G) {S S₀ : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) (hS₀S : S₀ ≤ S) [S₀.Normal]
    [(S ⊓ centralizer (S₀ : Set G)).Normal] (hES₀ : S ⊓ centralizer (S₀ : Set G) ≤ S₀) :
    fusionStronglyClosed ((rcSet S P : Subgroup G) : Set G) P := by
  intro x hx g hxg
  set K := centralizer (S₀ : Set G)
  set H := hSet S K (S ⊓ K)
  have hCK : centralizer (S : Set G) ≤ K := Subgroup.centralizer_le hS₀S
  have hxKK : x ∈ ⁅K, K⁆ := Subgroup.commutator_mono hCK hCK hx.1
  have hyKK : g⁻¹ * x * g ∈ ⁅K, K⁆ := by
    have := (Subgroup.commutator_normal K K).conj_mem x hxKK g⁻¹
    simpa using this
  have hyK : g⁻¹ * x * g ∈ K := Subgroup.commutator_le_self K hyKK
  have hyH := commutator_inf_le_hSet P hSP hS hES₀ ⟨hyKK, hxg, hyK⟩
  have hEH : S ⊓ K ≤ centralizer (H : Set G) := fun e he =>
    mem_centralizer_iff.mpr fun h hh => (mem_centralizer_iff.mp (hSet_le S K _ hh) e
      (hES₀ he)).symm
  have hHC := commutator_le_centralizer_of_le (commutator_le_of_hSet S K (S ⊓ K)) hEH
  obtain ⟨m, hm, hmeq⟩ :=
    exists_normalizer_conj P hSP hS (rcSet_le_centralizer S P hx) (hHC hyH)
  rw [← hmeq]
  exact conj_mem_rcSet hm hx (by rw [hmeq]; exact hxg)

end CFSG.Goldschmidt75
