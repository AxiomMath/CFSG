module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Helpers

variable {G : Type*} [Group G]

private theorem g7_pCoreOf_le (p : ℕ) (H : Subgroup G) : pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

private theorem g7_isPGroup_pCoreOf (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreOf p H) :=
  (CFSG.pCore_isPGroup (p := p) (G := H)).map H.subtype

private theorem g7_conj_mem_pCoreOf (p : ℕ) (H : Subgroup G) {h y : G} (hh : h ∈ H)
    (hy : y ∈ pCoreOf p H) : h * y * h⁻¹ ∈ pCoreOf p H := by
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
  have := (CFSG.pCore_normal (p := p) (G := H)).conj_mem y' hy' ⟨h, hh⟩
  exact Subgroup.mem_map.2 ⟨_, this, rfl⟩

private theorem g7_le_pCoreOf {p : ℕ} {N H : Subgroup G} (hNH : N ≤ H)
    (hH : H ≤ Subgroup.normalizer (N : Set G)) (hp : IsPGroup p N) : N ≤ pCoreOf p H := by
  have hnorm : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hH
  have hpg : IsPGroup p (N.subgroupOf H) := hp.comap_subtype
  have : N.subgroupOf H ≤ CFSG.pCore p H := le_sSup ⟨hnorm, hpg⟩
  calc N = (N.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hNH).symm
    _ ≤ (CFSG.pCore p H).map H.subtype := Subgroup.map_mono this

private theorem g7_le_normalizer_of_conj {N S : Subgroup G}
    (h : ∀ n ∈ N, ∀ x ∈ S, n * x * n⁻¹ ∈ S) : N ≤ Subgroup.normalizer (S : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h n hn x hx, fun hx => ?_⟩
  have := h n⁻¹ (N.inv_mem hn) _ hx
  simpa [mul_assoc] using this

private theorem g7_map_mem_pCoreOf (p : ℕ) (H : Subgroup G) (φ : G ≃* G)
    (hφ : ∀ h, h ∈ H ↔ φ h ∈ H) {y : G} (hy : y ∈ pCoreOf p H) : φ y ∈ pCoreOf p H := by
  have hle : (pCoreOf p H).map φ.toMonoidHom ≤ pCoreOf p H := by
    refine g7_le_pCoreOf ?_ ?_ ?_
    · rintro _ ⟨y', hy', rfl⟩
      exact (hφ y').1 (g7_pCoreOf_le p H hy')
    · apply g7_le_normalizer_of_conj
      rintro h hh _ ⟨y', hy', rfl⟩
      have hh' : φ.symm h ∈ H := by
        rw [hφ]; simpa using hh
      refine ⟨_, g7_conj_mem_pCoreOf p H hh' hy', ?_⟩
      simp
    · exact (g7_isPGroup_pCoreOf p H).map _
  exact hle ⟨y, hy, rfl⟩

private theorem g7_exists_pow_of_mem_pCoreOf (p : ℕ) (H : Subgroup G) {y : G}
    (hy : y ∈ pCoreOf p H) : ∃ j : ℕ, y ^ (p ^ j) = 1 := by
  obtain ⟨j, hj⟩ := g7_isPGroup_pCoreOf p H ⟨y, hy⟩
  exact ⟨j, by simpa using congrArg Subtype.val hj⟩

private theorem g7_pCoreOf_subgroupOf (p : ℕ) {H K : Subgroup G} (hHK : H ≤ K) :
    (pCoreOf p H).subgroupOf K = pCoreOf p (H.subgroupOf K) := by
  apply le_antisymm
  · have h1 : (pCoreOf p H).subgroupOf K ≤ H.subgroupOf K := fun x hx =>
      Subgroup.mem_subgroupOf.2 (g7_pCoreOf_le p H (Subgroup.mem_subgroupOf.1 hx))
    refine g7_le_pCoreOf h1 ?_ (g7_isPGroup_pCoreOf p H).comap_subtype
    apply g7_le_normalizer_of_conj
    intro h hh x hx
    exact g7_conj_mem_pCoreOf p H (Subgroup.mem_subgroupOf.1 hh) (Subgroup.mem_subgroupOf.1 hx)
  · intro x hx
    have hN : (pCoreOf p (H.subgroupOf K)).map K.subtype ≤ pCoreOf p H := by
      refine g7_le_pCoreOf ?_ ?_ ((g7_isPGroup_pCoreOf p (H.subgroupOf K)).map _)
      · rintro _ ⟨y, hy, rfl⟩
        exact Subgroup.mem_subgroupOf.1 (g7_pCoreOf_le p _ hy)
      · apply g7_le_normalizer_of_conj
        rintro h hh _ ⟨y, hy, rfl⟩
        have hhK : h ∈ K := hHK hh
        refine ⟨⟨h, hhK⟩ * y * ⟨h, hhK⟩⁻¹, ?_, rfl⟩
        exact g7_conj_mem_pCoreOf p _ (Subgroup.mem_subgroupOf.2 hh) hy
    exact Subgroup.mem_subgroupOf.2 (hN (Subgroup.mem_map.2 ⟨x, hx, rfl⟩))

private theorem g7_map_pCoreOf_eq_of_central {G B : Type*} [Group G] [Group B] (π : G →* B)
    (Y : Subgroup G) [Finite Y] (T : Subgroup B) (hT : IsPGroup 2 T) (hYT : Y.map π = T)
    (hker : ∀ y ∈ Y, π y = 1 → ∀ g ∈ Y, g * y = y * g) :
    (pCoreOf 2 Y).map π = T := by
  have hmem : ∀ y : Y, π (y : G) ∈ T := fun y => hYT ▸ Subgroup.mem_map_of_mem π y.2
  let f : Y →* T := (π.comp Y.subtype).codRestrict T hmem
  have hfc : ∀ y : Y, ((f y : T) : B) = π (y : G) := fun y => rfl
  have hf : Function.Surjective f := by
    rintro ⟨t, ht⟩
    obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.1 (hYT ▸ ht)
    exact ⟨⟨y, hy⟩, Subtype.ext hyt⟩
  let S : Sylow 2 Y := Classical.arbitrary _
  have hSf : S.map f = ⊤ := by
    have h1 : IsPGroup 2 (⊤ : Subgroup T) := hT.of_equiv Subgroup.topEquiv.symm
    exact ((Sylow.mapSurjective hf S).is_maximal' h1 le_top).symm
  have hnorm : (S : Subgroup Y).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : f g ∈ S.map f := hSf ▸ Subgroup.mem_top _
    obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.1 hg
    have hz : f (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
    have hz' : π ((s⁻¹ * g : Y) : G) = 1 := by
      have := congrArg Subtype.val hz
      rw [hfc] at this
      exact this
    have hc := hker _ (s⁻¹ * g).2 hz'
    have hcY : ∀ w : Y, w * (s⁻¹ * g) = (s⁻¹ * g) * w := fun w => Subtype.ext (hc w w.2)
    have hgs : g = s * (s⁻¹ * g) := by group
    have : g * x * g⁻¹ = s * x * s⁻¹ := by
      rw [hgs]
      have := hcY x
      calc s * (s⁻¹ * g) * x * (s * (s⁻¹ * g))⁻¹
          = s * ((s⁻¹ * g) * x * (s⁻¹ * g)⁻¹) * s⁻¹ := by group
        _ = s * x * s⁻¹ := by rw [← this]; group
    rw [this]
    exact S.mul_mem (S.mul_mem hs hx) (S.inv_mem hs)
  have hSle : (S : Subgroup Y) ≤ CFSG.pCore 2 Y := le_sSup ⟨hnorm, S.isPGroup'⟩
  apply le_antisymm
  · rw [← hYT]
    exact Subgroup.map_mono (g7_pCoreOf_le 2 Y)
  · rintro t ht
    have : (⟨t, ht⟩ : T) ∈ S.map f := hSf ▸ Subgroup.mem_top _
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.1 this
    refine Subgroup.mem_map.2 ⟨(s : G), ?_, ?_⟩
    · exact Subgroup.mem_map.2 ⟨s, hSle hs, rfl⟩
    · have := congrArg Subtype.val hst
      rw [hfc] at this
      exact this

private theorem g7_map_pCoreOf_fixed {G A : Type*} [Group G] [Finite G] [Group A]
    (π : G →* A) (hπ : Function.Surjective π)
    (hker : ∀ g, π g = 1 → ∀ h, h * g = g * h)
    (hodd : ∀ z : G, (∀ h, h * z = z * h) → ∀ j : ℕ, z ^ (2 ^ j) = 1 → z = 1)
    (α : G ≃* G) (c : A) (hα : ∀ g, π (α g) = c * π g * c⁻¹)
    (C : Subgroup G) (hC : ∀ g, g ∈ C ↔ α g = g) :
    (pCoreOf 2 C).map π = pCoreOf 2 (Subgroup.centralizer ({c} : Set A)) := by
  set N : Subgroup A := Subgroup.centralizer ({c} : Set A) with hN
  have F1 : ∀ g, π g ∈ N ↔ π (α g) = π g := by
    intro g
    rw [hN, Subgroup.mem_centralizer_singleton_iff, hα]
    constructor
    · intro h
      rw [← h, mul_inv_cancel_right]
    · intro h
      calc π g * c = c * π g * c⁻¹ * c := by rw [h]
        _ = c * π g := by group
  have F2 : ∀ g, π g ∈ N → ∀ h, h * (α g * g⁻¹) = (α g * g⁻¹) * h := by
    intro g hg h
    refine hker (α g * g⁻¹) ?_ h
    rw [map_mul, map_inv, (F1 g).1 hg, mul_inv_cancel]
  have F3 : ∀ g, π g ∈ N → ∀ k ∈ C, g * k * g⁻¹ ∈ C := by
    intro g hg k hk
    rw [hC] at hk ⊢
    have hzc := F2 g hg
    have hαg : α g = (α g * g⁻¹) * g := by group
    calc α (g * k * g⁻¹) = α g * α k * (α g)⁻¹ := by simp [map_mul, map_inv]
      _ = ((α g * g⁻¹) * g) * k * ((α g * g⁻¹) * g)⁻¹ := by
          rw [hk]; nth_rewrite 1 [hαg]; nth_rewrite 2 [hαg]; rfl
      _ = (α g * g⁻¹) * (g * k * g⁻¹) * (α g * g⁻¹)⁻¹ := by group
      _ = (g * k * g⁻¹) * (α g * g⁻¹) * (α g * g⁻¹)⁻¹ := by rw [← hzc (g * k * g⁻¹)]
      _ = g * k * g⁻¹ := by group
  have F4 : ∀ g, π g ∈ N → g ∈ Subgroup.normalizer (C : Set G) := by
    intro g hg
    have : N.comap π ≤ Subgroup.normalizer (C : Set G) :=
      g7_le_normalizer_of_conj (fun n hn x hx => F3 n hn x hx)
    exact this hg
  have hle1 : (pCoreOf 2 C).map π ≤ pCoreOf 2 N := by
    refine g7_le_pCoreOf ?_ ?_ ((g7_isPGroup_pCoreOf 2 C).map π)
    · rintro _ ⟨r, hr, rfl⟩
      have hrC := g7_pCoreOf_le 2 C hr
      exact (F1 r).2 (by rw [(hC r).1 hrC])
    · apply g7_le_normalizer_of_conj
      rintro n hn _ ⟨r, hr, rfl⟩
      obtain ⟨g, rfl⟩ := hπ n
      have hg : g ∈ Subgroup.normalizer (C : Set G) := F4 g hn
      refine ⟨g * r * g⁻¹, ?_, by simp⟩
      exact g7_map_mem_pCoreOf 2 C (MulAut.conj g) (fun h => Subgroup.mem_normalizer_iff.1 hg h) hr
  have hle2 : pCoreOf 2 N ≤ (pCoreOf 2 C).map π := by
    have hTN : pCoreOf 2 N ≤ N := g7_pCoreOf_le 2 N
    have hcN : c ∈ N := by rw [hN]; exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    let Y₀ : Subgroup G := (pCoreOf 2 N).comap π
    have hY₀T : Y₀.map π = pCoreOf 2 N := Subgroup.map_comap_eq_self_of_surjective hπ _
    have hP₀ : (pCoreOf 2 Y₀).map π = pCoreOf 2 N :=
      g7_map_pCoreOf_eq_of_central π Y₀ (pCoreOf 2 N) (g7_isPGroup_pCoreOf 2 N) hY₀T
        (fun y _ hy g _ => hker y hy g)
    have hY₀α : ∀ g, g ∈ Y₀ ↔ α g ∈ Y₀ := by
      intro g
      simp only [Y₀, Subgroup.mem_comap]
      constructor
      · intro h
        rw [(F1 g).1 (hTN h)]; exact h
      · intro h
        rw [hα] at h
        have := g7_conj_mem_pCoreOf 2 N (N.inv_mem hcN) h
        simpa [mul_assoc] using this
    have hP₀α : ∀ y ∈ pCoreOf 2 Y₀, α y ∈ pCoreOf 2 Y₀ :=
      fun y hy => g7_map_mem_pCoreOf 2 Y₀ α hY₀α hy
    have hP₀C : pCoreOf 2 Y₀ ≤ C := by
      intro y hy
      have hyY : y ∈ Y₀ := g7_pCoreOf_le 2 Y₀ hy
      have hπy : π y ∈ N := hTN hyY
      rw [hC]
      have hz := F2 y hπy
      have hzP : α y * y⁻¹ ∈ pCoreOf 2 Y₀ :=
        (pCoreOf 2 Y₀).mul_mem (hP₀α y hy) ((pCoreOf 2 Y₀).inv_mem hy)
      obtain ⟨j, hj⟩ := g7_isPGroup_pCoreOf 2 Y₀ ⟨_, hzP⟩
      have hj' : (α y * y⁻¹) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
      exact mul_inv_eq_one.1 (hodd _ hz j hj')
    have hCP₀ : C ≤ Subgroup.normalizer (pCoreOf 2 Y₀ : Set G) := by
      apply g7_le_normalizer_of_conj
      intro g hg x hx
      have hπg : π g ∈ N := (F1 g).2 (by rw [(hC g).1 hg])
      refine g7_map_mem_pCoreOf 2 Y₀ (MulAut.conj g) ?_ hx
      intro h
      simp only [Y₀, Subgroup.mem_comap, MulAut.conj_apply, map_mul, map_inv]
      constructor
      · intro hh
        exact g7_conj_mem_pCoreOf 2 N hπg hh
      · intro hh
        have := g7_conj_mem_pCoreOf 2 N (N.inv_mem hπg) hh
        simpa [mul_assoc] using this
    have hP₀R : pCoreOf 2 Y₀ ≤ pCoreOf 2 C :=
      g7_le_pCoreOf hP₀C hCP₀ (g7_isPGroup_pCoreOf 2 Y₀)
    calc pCoreOf 2 N = (pCoreOf 2 Y₀).map π := hP₀.symm
      _ ≤ (pCoreOf 2 C).map π := Subgroup.map_mono hP₀R
  exact le_antisymm hle1 hle2

private theorem g7_mem_sup_of_commute {s t : Subgroup G}
    (hst : ∀ y ∈ s, ∀ z ∈ t, y * z = z * y) {x : G} :
    x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, x, hx, by simp⟩
    · exact ⟨1, s.one_mem, 1, t.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      refine ⟨y₁ * y₂, s.mul_mem hy₁ hy₂, z₁ * z₂, t.mul_mem hz₁ hz₂, ?_⟩
      calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
        _ = y₁ * (z₁ * y₂) * z₂ := by rw [hst y₂ hy₂ z₁ hz₁]
        _ = y₁ * z₁ * (y₂ * z₂) := by group
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      refine ⟨y⁻¹, s.inv_mem hy, z⁻¹, t.inv_mem hz, ?_⟩
      have : y * z = z * y := hst y hy z hz
      calc y⁻¹ * z⁻¹ = (z * y)⁻¹ := by group
        _ = (y * z)⁻¹ := by rw [this]
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

private theorem g7_pow_two_pow_of_le {a : G} {i k : ℕ} (h : a ^ (2 ^ i) = 1) (hik : i ≤ k) :
    a ^ (2 ^ k) = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one] at h ⊢
  exact h.trans (pow_dvd_pow 2 hik)

private theorem g7_comm_mul_central_left {z : G} (hz : ∀ g, g * z = z * g) (s g : G) :
    ⁅s * z, g⁆ = ⁅s, g⁆ := by
  have hzg : z * g * z⁻¹ = g := by rw [← hz g, mul_inv_cancel_right]
  calc ⁅s * z, g⁆ = s * (z * g * z⁻¹) * s⁻¹ * g⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅s, g⁆ := by rw [hzg, commutatorElement_def]

private theorem g7_comm_mul_central_right {z : G} (hz : ∀ g, g * z = z * g) (s g : G) :
    ⁅g, s * z⁆ = ⁅g, s⁆ := by
  have hzg : z * g⁻¹ * z⁻¹ = g⁻¹ := by rw [← hz g⁻¹, mul_inv_cancel_right]
  calc ⁅g, s * z⁆ = g * s * (z * g⁻¹ * z⁻¹) * s⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅g, s⁆ := by rw [hzg, commutatorElement_def]

private theorem g7_commutator_mem {H : Subgroup G} {q a s : G}
    (hq : q ∈ Subgroup.normalizer (H : Set G)) (hs : s * q = q * s) (has : a * s ∈ H) :
    ⁅a, q⁆ ∈ H := by
  have h1 : q * (a * s)⁻¹ * q⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hq _).1 (H.inv_mem has)
  have h2 : (a * s) * (q * (a * s)⁻¹ * q⁻¹) ∈ H := H.mul_mem has h1
  have hsq : s * q * s⁻¹ = q := by rw [hs, mul_inv_cancel_right]
  have : ⁅a, q⁆ = (a * s) * (q * (a * s)⁻¹ * q⁻¹) :=
    calc ⁅a, q⁆ = a * q * a⁻¹ * q⁻¹ := commutatorElement_def a q
      _ = a * (s * q * s⁻¹) * a⁻¹ * q⁻¹ := by rw [hsq]
      _ = (a * s) * (q * (a * s)⁻¹ * q⁻¹) := by group
  rw [this]
  exact h2

private theorem g7_centralizer_le {c c₀ : G} (h : c₀ ∈ Subgroup.zpowers c) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.centralizer ({c₀} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  exact (Commute.zpow_right (show Commute x c from hx) m).eq

private theorem g7_not_isPGroup_alt7 : ¬ IsPGroup 2 ↥(alternatingGroup (Fin 7)) := by
  intro h
  have hcard : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]; simp [Nat.factorial]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h
  have h3 : 3 ∣ 2 ^ n := by rw [← hn, hcard]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end Helpers

section Gamma7

variable {X : Type} [Group X] [Finite X]

private def g7Pi {K : Subgroup X} (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) :
    ↥K →* ↥(alternatingGroup (Fin 7)) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))

private theorem g7Pi_apply {K : Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) (k : ↥K) :
    g7Pi e k = e (QuotientGroup.mk k) := rfl

private theorem g7Pi_surjective {K : Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) :
    Function.Surjective (g7Pi e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

private theorem g7Pi_eq_one_iff {K : Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) (k : ↥K) :
    g7Pi e k = 1 ↔ ∀ h : ↥K, h * k = k * h := by
  rw [g7Pi_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]

private theorem g7_imgA7_eq {K : Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) (R : Subgroup X) :
    imgA7 K R e = (R.subgroupOf K).map (g7Pi e) := by
  unfold imgA7 g7Pi
  rw [Subgroup.map_map]

private theorem g7_imgA7_mono {K : Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) {R R' : Subgroup X}
    (h : R ≤ R') : imgA7 K R e ≤ imgA7 K R' e := by
  rw [g7_imgA7_eq, g7_imgA7_eq]
  exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

private theorem g7_rootOf_le {K : Subgroup X} (d : X) : rootOf K d ≤ K :=
  (g7_pCoreOf_le 2 _).trans inf_le_left

private theorem g7_rootOf_pgroup {K : Subgroup X} (d : X) : IsPGroup 2 (rootOf K d) :=
  g7_isPGroup_pCoreOf 2 _

private theorem g7_center_two_pow {K : Subgroup X} (hK3 : GLAPPrimeCore 3 ↥K = ⊥) {z : ↥K}
    (hz : ∀ h, h * z = z * h) {j : ℕ} (hj : z ^ (2 ^ j) = 1) : z = 1 := by
  have hn : (Subgroup.zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g (z ^ m) := (show Commute g z from hz g).zpow_right m
    have : g * z ^ m * g⁻¹ = z ^ m := by rw [hc.eq]; group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) m
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hj)
      (Nat.Coprime.pow_right j (by norm_num))
  have hle : Subgroup.zpowers z ≤ GLAPPrimeCore 3 ↥K := le_sSup ⟨hn, hcop⟩
  rw [hK3] at hle
  exact Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers z))

private theorem g7_two_elt_central {K : Subgroup X} (hK3 : GLAPPrimeCore 3 ↥K = ⊥) {r x : X}
    (hrK : r ∈ K) (hxK : x ∈ K) (hz : r⁻¹ * x ∈ Subgroup.centralizer (K : Set X)) {i j : ℕ}
    (hr : r ^ (2 ^ i) = 1) (hx : x ^ (2 ^ j) = 1) : r = x := by
  set r' : ↥K := ⟨r, hrK⟩ with hr'
  set x' : ↥K := ⟨x, hxK⟩ with hx'
  have hz' : ∀ h : ↥K, h * (r'⁻¹ * x') = (r'⁻¹ * x') * h := by
    intro h
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hz h h.2
  have hr2 : r' ^ (2 ^ i) = 1 := Subtype.ext (by simpa [hr'] using hr)
  have hx2 : x' ^ (2 ^ j) = 1 := Subtype.ext (by simpa [hx'] using hx)
  have hrx : Commute r' x' := by
    have hzr : r' * (r'⁻¹ * x') = (r'⁻¹ * x') * r' := hz' r'
    show r' * x' = x' * r'
    calc r' * x' = r' * (r' * (r'⁻¹ * x')) := by group
      _ = r' * ((r'⁻¹ * x') * r') := by rw [hzr]
      _ = x' * r' := by group
  have hcom : Commute r'⁻¹ x' := hrx.inv_left
  have hrk : r' ^ (2 ^ max i j) = 1 := g7_pow_two_pow_of_le hr2 (le_max_left i j)
  have hxk : x' ^ (2 ^ max i j) = 1 := g7_pow_two_pow_of_le hx2 (le_max_right i j)
  have h1 : (r'⁻¹ * x') ^ (2 ^ max i j) = 1 := by
    rw [hcom.mul_pow, inv_pow, hrk, inv_one, one_mul, hxk]
  have h2 := g7_center_two_pow hK3 hz' h1
  have : r' = x' := inv_mul_eq_one.1 h2
  exact congrArg Subtype.val this

private theorem g7_inf_le_root {K : Subgroup X} (hK3 : GLAPPrimeCore 3 ↥K = ⊥) {R Y : Subgroup X}
    (hRK : R ≤ K) (hR : IsPGroup 2 R) (hY : IsPGroup 2 Y)
    (hYle : Y ≤ R ⊔ Subgroup.centralizer (K : Set X)) : Y ⊓ K ≤ R := by
  rintro x ⟨hxY, hxK⟩
  obtain ⟨r, hr, s, hs, hrs⟩ :=
    (g7_mem_sup_of_commute (fun y hy z hz => Subgroup.mem_centralizer_iff.1 hz y (hRK hy))).1
      (hYle hxY)
  have hrK : r ∈ K := hRK hr
  have hsx : r⁻¹ * x = s := by rw [← hrs]; group
  obtain ⟨i, hi⟩ := hR ⟨r, hr⟩
  obtain ⟨j, hj⟩ := hY ⟨x, hxY⟩
  have hi' : r ^ (2 ^ i) = 1 := by simpa using congrArg Subtype.val hi
  have hj' : x ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have := g7_two_elt_central hK3 hrK hxK (by rw [hsx]; exact hs) hi' hj'
  rw [← this]
  exact hr

private theorem g7_comm_of_mem {D : Subgroup X} (hD : IsElemAbelian 3 D) {d d' : X} (hd : d ∈ D)
    (hd' : d' ∈ D) : d * d' = d' * d :=
  congrArg Subtype.val (hD.1.is_comm.comm (⟨d, hd⟩ : D) ⟨d', hd'⟩)

private theorem g7_orderOf_eq_three {D : Subgroup X} (hD : IsElemAbelian 3 D) {d : X} (hdD : d ∈ D)
    (hd1 : d ≠ 1) : orderOf d = 3 := by
  have h3 : d ^ 3 = 1 := hD.2 d hdD
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hd1
  · exact h

private theorem g7_conj_comm {K : Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) {d₁ d₂ : X}
    (h₁ : d₁ ∈ Subgroup.normalizer (K : Set X)) (h₂ : d₂ ∈ Subgroup.normalizer (K : Set X))
    (hcomm : d₁ * d₂ = d₂ * d₁) {c₁ c₂ : ↥(alternatingGroup (Fin 7))}
    (hc₁ : ConjActsAs d₁ K e c₁) (hc₂ : ConjActsAs d₂ K e c₂) : c₁ * c₂ = c₂ * c₁ := by
  have hcen : Subgroup.center ↥(alternatingGroup (Fin 7)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have key : ∀ a : ↥(alternatingGroup (Fin 7)),
      (c₁ * c₂) * a * (c₁ * c₂)⁻¹ = (c₂ * c₁) * a * (c₂ * c₁)⁻¹ := by
    intro a
    obtain ⟨k, rfl⟩ := g7Pi_surjective e a
    let k₂ : ↥K := ⟨d₂ * k * d₂⁻¹, (Subgroup.mem_normalizer_iff.1 h₂ k).1 k.2⟩
    let k₁ : ↥K := ⟨d₁ * k * d₁⁻¹, (Subgroup.mem_normalizer_iff.1 h₁ k).1 k.2⟩
    let k₁₂ : ↥K := ⟨d₁ * k₂ * d₁⁻¹, (Subgroup.mem_normalizer_iff.1 h₁ k₂).1 k₂.2⟩
    let k₂₁ : ↥K := ⟨d₂ * k₁ * d₂⁻¹, (Subgroup.mem_normalizer_iff.1 h₂ k₁).1 k₁.2⟩
    have hk12 : k₁₂ = k₂₁ := Subtype.ext (by
      show d₁ * (d₂ * (k : X) * d₂⁻¹) * d₁⁻¹ = d₂ * (d₁ * (k : X) * d₁⁻¹) * d₂⁻¹
      calc d₁ * (d₂ * (k : X) * d₂⁻¹) * d₁⁻¹ = (d₁ * d₂) * k * (d₁ * d₂)⁻¹ := by group
        _ = (d₂ * d₁) * k * (d₂ * d₁)⁻¹ := by rw [hcomm]
        _ = d₂ * (d₁ * (k : X) * d₁⁻¹) * d₂⁻¹ := by group)
    have e2 : g7Pi e k₂ = c₂ * g7Pi e k * c₂⁻¹ := hc₂ k k₂ rfl
    have e1 : g7Pi e k₁ = c₁ * g7Pi e k * c₁⁻¹ := hc₁ k k₁ rfl
    have e12 : g7Pi e k₁₂ = c₁ * g7Pi e k₂ * c₁⁻¹ := hc₁ k₂ k₁₂ rfl
    have e21 : g7Pi e k₂₁ = c₂ * g7Pi e k₁ * c₂⁻¹ := hc₂ k₁ k₂₁ rfl
    have h12 : c₁ * (c₂ * g7Pi e k * c₂⁻¹) * c₁⁻¹ = c₂ * (c₁ * g7Pi e k * c₁⁻¹) * c₂⁻¹ := by
      rw [← e2, ← e1, ← e12, ← e21, hk12]
    calc (c₁ * c₂) * g7Pi e k * (c₁ * c₂)⁻¹ = c₁ * (c₂ * g7Pi e k * c₂⁻¹) * c₁⁻¹ := by group
      _ = c₂ * (c₁ * g7Pi e k * c₁⁻¹) * c₂⁻¹ := h12
      _ = (c₂ * c₁) * g7Pi e k * (c₂ * c₁)⁻¹ := by group
  have hmem : (c₂ * c₁)⁻¹ * (c₁ * c₂) ∈ Subgroup.center ↥(alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    calc a * ((c₂ * c₁)⁻¹ * (c₁ * c₂))
        = (c₂ * c₁)⁻¹ * ((c₂ * c₁) * a * (c₂ * c₁)⁻¹) * (c₁ * c₂) := by group
      _ = (c₂ * c₁)⁻¹ * ((c₁ * c₂) * a * (c₁ * c₂)⁻¹) * (c₁ * c₂) := by rw [key a]
      _ = ((c₂ * c₁)⁻¹ * (c₁ * c₂)) * a := by group
  rw [hcen, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.1 hmem).symm

end Gamma7

section Gamma7Leaves

variable {X : Type} [Group X] [Finite X]

theorem imgA7_rootOf {K : Subgroup X} (hK : IsComponentOf K ⊤) (hK3 : GLAPPrimeCore 3 ↥K = ⊥)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) {d : X} (hd : orderOf d = 3)
    (hdN : d ∈ Subgroup.normalizer (K : Set X)) {c : ↥(alternatingGroup (Fin 7))}
    (hc : ConjActsAs d K e c) :
    imgA7 K (rootOf K d) e =
      pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7)))) := by
  clear hK hd
  let α : ↥K ≃* ↥K := K.normalizerMonoidHom ⟨d, hdN⟩
  have hα : ∀ k : ↥K, ((α k : ↥K) : X) = d * k * d⁻¹ := fun k => rfl
  have hcα : ∀ k : ↥K, g7Pi e (α k) = c * g7Pi e k * c⁻¹ := fun k => hc k (α k) (hα k)
  let C : Subgroup ↥K := (K ⊓ Subgroup.centralizer ({d} : Set X)).subgroupOf K
  have hC : ∀ g : ↥K, g ∈ C ↔ α g = g := by
    intro g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      ← Subtype.coe_inj, hα]
    constructor
    · rintro ⟨_, h⟩
      rw [← h, mul_inv_cancel_right]
    · intro h
      refine ⟨g.2, ?_⟩
      calc (g : X) * d = (d * g * d⁻¹) * d := by rw [h]
        _ = d * g := by group
  have hmain := g7_map_pCoreOf_fixed (g7Pi e) (g7Pi_surjective e)
    (fun g hg => (g7Pi_eq_one_iff e g).1 hg)
    (fun z hz j hj => g7_center_two_pow hK3 hz hj) α c hcα C hC
  have hsub : (rootOf K d).subgroupOf K = pCoreOf 2 C := g7_pCoreOf_subgroupOf 2 inf_le_left
  rw [g7_imgA7_eq, hsub]
  exact hmain

theorem gamma7_local_le (h1 : Input19_21_1) {K D : Subgroup X} {Hf : X → Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) (hd : Gamma7Data K D Hf)
    {d : X} (hdD : d ∈ D) (hd1 : d ≠ 1) (hne : ¬ Hf d ≤ Subgroup.centralizer (K : Set X)) :
    d ∈ Subgroup.normalizer (K : Set X) ∧
      (∃ c : ↥(alternatingGroup (Fin 7)), (c : Equiv.Perm (Fin 7)).IsThreeCycle ∧
          ConjActsAs d K e c) ∧
      IsRootFour (imgA7 K (rootOf K d) e) ∧ Hf d ≤ rootOf K d ⊔ Subgroup.centralizer (K : Set X) := by
  have hord : orderOf d = 3 := g7_orderOf_eq_three hd.fam.elemAbelian hdD hd1
  obtain ⟨hdN, hTN, hc, hroot, hind⟩ := h1 X 3 Nat.prime_three (by norm_num) K hd.comp hd.o3 e d
    hord (Hf d) (hd.fam.le_pCore d hdD hd1) hne
  refine ⟨hdN, hc, hroot, ?_⟩
  intro t ht
  have htN : t ∈ Subgroup.normalizer (K : Set X) := hTN ht
  have hmem : K.normalizerMonoidHom ⟨t, htN⟩ ∈ inducedAutGroup (Hf d) K :=
    Subgroup.mem_map.2 ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
  obtain ⟨r, hr, hrt⟩ := Subgroup.mem_map.1 (hind hmem)
  have hrR : (r : X) ∈ rootOf K d := Subgroup.mem_subgroupOf.1 hr
  have hcomm : ∀ k : ↥K, (r : X) * k * (r : X)⁻¹ = t * k * t⁻¹ := by
    intro k
    have h := congrArg (fun φ : MulAut ↥K => ((φ k : ↥K) : X)) hrt
    exact h
  have hs : (r : X)⁻¹ * t ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := hcomm ⟨k, hk⟩
    have h2 : (r : X)⁻¹ * (t * k * t⁻¹) * r = k := by rw [← h1]; group
    calc k * ((r : X)⁻¹ * t) = ((r : X)⁻¹ * (t * k * t⁻¹) * r) * ((r : X)⁻¹ * t) := by rw [h2]
      _ = ((r : X)⁻¹ * t) * k := by group
  have : t = (r : X) * ((r : X)⁻¹ * t) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hrR hs

theorem gamma7_local_ge (hA : A7Facts) (hM : AltSixSevenCentre)
    {K D : Subgroup X} {Hf : X → Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) (hd : Gamma7Data K D Hf)
    {d : X} (hdD : d ∈ D) (hd1 : d ≠ 1) (hne : ¬ Hf d ≤ Subgroup.centralizer (K : Set X))
    (hdN : d ∈ Subgroup.normalizer (K : Set X)) {c : ↥(alternatingGroup (Fin 7))}
    (hc3 : (c : Equiv.Perm (Fin 7)).IsThreeCycle) (hc : ConjActsAs d K e c)
    (hle : Hf d ≤ rootOf K d ⊔ Subgroup.centralizer (K : Set X)) : rootOf K d ≤ Hf d := by
  by_cases hH : IsHatSeven ↥K
  · exact hd.hatb hH d hdD hd1 hdN
  have hord : orderOf d = 3 := g7_orderOf_eq_three hd.fam.elemAbelian hdD hd1
  have hK3 := hd.o3
  have hperf : commutator ↥K = ⊤ := hd.comp.2.2.1
  have hZ : Subgroup.center ↥K = ⊥ := by
    have hdvd : Nat.card (Subgroup.center ↥K) ∣ 6 := hM 7 (Or.inr rfl) ↥K hperf ⟨e⟩
    have hodd : ¬ 2 ∣ Nat.card (Subgroup.center ↥K) := by
      intro h2
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥K)) 2 h2
      have hxo : orderOf (x : ↥K) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
      have hz : (x : ↥K) ^ (2 ^ 1) = 1 := by
        rw [pow_one]; rw [← hxo]; exact pow_orderOf_eq_one _
      have := g7_center_two_pow hK3 (fun h => Subgroup.mem_center_iff.1 x.2 h) hz
      rw [this, orderOf_one] at hxo
      omega
    have h3 : Nat.card (Subgroup.center ↥K) ∣ 3 := by
      have : Nat.card (Subgroup.center ↥K) ∣ 2 * 3 := hdvd
      exact (Nat.Coprime.dvd_of_dvd_mul_left
        ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd))) this)
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exact absurd ⟨hperf, h, ⟨e⟩⟩ hH
  have hinj : Function.Injective (g7Pi e) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have := (g7Pi_eq_one_iff e k).1 hk
    have hk' : k ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.2 this
    rw [hZ] at hk'
    exact Subgroup.mem_bot.1 hk'
  have hT := imgA7_rootOf hd.comp hK3 e hord hdN hc
  obtain ⟨t, htH, htC⟩ := Set.not_subset.1 hne
  obtain ⟨r, hr, s, hs, hrs⟩ :=
    (g7_mem_sup_of_commute (fun y hy z hz =>
      Subgroup.mem_centralizer_iff.1 hz y (g7_rootOf_le d hy))).1 (hle htH)
  have hrK : r ∈ K := g7_rootOf_le d hr
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply htC
    rw [← hrs, one_mul]
    exact hs
  set r' : ↥K := ⟨r, hrK⟩ with hr'
  have hπr : g7Pi e r' ∈ pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7)))) := by
    rw [← hT, g7_imgA7_eq]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hr)
  have hπr1 : g7Pi e r' ≠ 1 := by
    intro h
    apply hr1
    have : r' = 1 := hinj (by rw [h, map_one])
    exact congrArg Subtype.val this
  obtain ⟨Q, -, -, hQc, hQcomm⟩ := hA.2.1 c hc3
  have hcomm : ⁅Subgroup.zpowers (g7Pi e r'), Q⁆ =
      pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7)))) :=
    hQcomm (g7Pi e r') hπr hπr1
  have hU : ∀ i : ℤ, ∀ q ∈ Q.comap (g7Pi e), ⁅r' ^ i, q⁆ ∈ (Hf d).subgroupOf K := by
    intro i q hq
    have hq' : g7Pi e q ∈ Q := hq
    have hqd : d * (q : X) * d⁻¹ = q := by
      have h1 : g7Pi e ⟨d * (q : X) * d⁻¹, (Subgroup.mem_normalizer_iff.1 hdN q).1 q.2⟩ =
          c * g7Pi e q * c⁻¹ := hc q _ rfl
      have h2 : c * g7Pi e q * c⁻¹ = g7Pi e q := by
        have := hQc hq'
        rw [Subgroup.mem_centralizer_singleton_iff] at this
        rw [← this, mul_inv_cancel_right]
      exact congrArg Subtype.val (hinj (h1.trans h2))
    have hqcent : (q : X) ∈ Subgroup.centralizer ({d} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.1 hqd).symm
    have hqN : (q : X) ∈ Subgroup.normalizer (Hf d : Set X) := hd.cinv d hdD hd1 q hqcent
    have hrs' : (r : X) * s = s * r := Subgroup.mem_centralizer_iff.1 hs r hrK
    have hts : t ^ i = (r : X) ^ i * s ^ i := by
      rw [← hrs]; exact (Commute.mul_zpow (show Commute (r : X) s from hrs') i)
    have hti : (r : X) ^ i * s ^ i ∈ Hf d := hts ▸ (Hf d).zpow_mem htH i
    have hsi : (q : X) * s ^ i = s ^ i * q :=
      Subgroup.mem_centralizer_iff.1 ((Subgroup.centralizer (K : Set X)).zpow_mem hs i) q q.2
    have := g7_commutator_mem hqN hsi.symm hti
    rw [Subgroup.mem_subgroupOf]
    have h3 : ((⁅r' ^ i, q⁆ : ↥K) : X) = ⁅(r : X) ^ i, (q : X)⁆ := by
      simp [commutatorElement_def, hr']
    rw [h3]
    exact this
  have hcomm_le : ⁅Subgroup.zpowers r', Q.comap (g7Pi e)⁆ ≤ (Hf d).subgroupOf K := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₁
    exact hU i g₂ hg₂
  have hmap : (⁅Subgroup.zpowers r', Q.comap (g7Pi e)⁆).map (g7Pi e) =
      pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7)))) := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers,
      Subgroup.map_comap_eq_self_of_surjective (g7Pi_surjective e)]
    exact hcomm
  have hTle : pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7)))) ≤
      ((Hf d).subgroupOf K).map (g7Pi e) := hmap ▸ Subgroup.map_mono hcomm_le
  intro ρ hρ
  have hρK : ρ ∈ K := g7_rootOf_le d hρ
  have hρT : g7Pi e ⟨ρ, hρK⟩ ∈
      pCoreOf 2 (Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7)))) := by
    rw [← hT, g7_imgA7_eq]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hρ)
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 (hTle hρT)
  have : u = ⟨ρ, hρK⟩ := hinj hu'
  have hu2 : (u : X) ∈ Hf d := Subgroup.mem_subgroupOf.1 hu
  rw [this] at hu2
  exact hu2

theorem gamma7_local (hA : A7Facts) (hM : AltSixSevenCentre) (h1 : Input19_21_1)
    {K D : Subgroup X} {Hf : X → Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) (hd : Gamma7Data K D Hf)
    {d : X} (hdD : d ∈ D) (hd1 : d ≠ 1) :
    Hf d ≤ Subgroup.centralizer (K : Set X) ∨
      (rootOf K d ≤ Hf d ∧ Hf d ≤ rootOf K d ⊔ Subgroup.centralizer (K : Set X) ∧
        d ∈ Subgroup.normalizer (K : Set X) ∧
        ∃ c : ↥(alternatingGroup (Fin 7)), (c : Equiv.Perm (Fin 7)).IsThreeCycle ∧
          ConjActsAs d K e c ∧ IsRootFour (imgA7 K (rootOf K d) e)) := by
  by_cases hc : Hf d ≤ Subgroup.centralizer (K : Set X)
  · exact Or.inl hc
  · obtain ⟨hN, ⟨c, hc3, hcc⟩, hroot, hle⟩ := gamma7_local_le h1 e hd hdD hd1 hc
    exact Or.inr ⟨gamma7_local_ge hA hM e hd hdD hd1 hc hN hc3 hcc hle, hle, hN, c, hc3, hcc, hroot⟩

private theorem g7_hf_pgroup {K D : Subgroup X} {Hf : X → Subgroup X} (hd : Gamma7Data K D Hf)
    {d : X} (hdD : d ∈ D) (hd1 : d ≠ 1) : IsPGroup 2 (Hf d) :=
  (g7_isPGroup_pCoreOf 2 _).to_le (hd.fam.le_pCore d hdD hd1)

private theorem g7_inf_eq_bot {K D : Subgroup X} {Hf : X → Subgroup X} (hd : Gamma7Data K D Hf)
    {d : X} (hdD : d ∈ D) (hd1 : d ≠ 1) (hC : Hf d ≤ Subgroup.centralizer (K : Set X)) :
    Hf d ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxH, hxK⟩
  obtain ⟨j, hj⟩ := g7_hf_pgroup hd hdD hd1 ⟨x, hxH⟩
  have hj' : x ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hcen : ∀ h : ↥K, h * (⟨x, hxK⟩ : ↥K) = ⟨x, hxK⟩ * h := fun h =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 (hC hxH) h h.2)
  have := g7_center_two_pow hd.o3 hcen (j := j) (Subtype.ext (by simpa using hj'))
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

private theorem g7_inf_eq_root (hA : A7Facts) (hM : AltSixSevenCentre) (h1 : Input19_21_1)
    {K D : Subgroup X} {Hf : X → Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) (hd : Gamma7Data K D Hf)
    {d : X} (hdD : d ∈ D) (hd1 : d ≠ 1) (hne : ¬ Hf d ≤ Subgroup.centralizer (K : Set X)) :
    Hf d ⊓ K = rootOf K d := by
  rcases gamma7_local hA hM h1 e hd hdD hd1 with hC | ⟨hge, hle, -⟩
  · exact absurd hC hne
  · apply le_antisymm
    · exact g7_inf_le_root hd.o3 (g7_rootOf_le d) (g7_rootOf_pgroup d) (g7_hf_pgroup hd hdD hd1) hle
    · exact le_inf hge (g7_rootOf_le d)

theorem gamma7_sigma_le (hA : A7Facts) (hM : AltSixSevenCentre) (h1 : Input19_21_1)
    {K D : Subgroup X} {Hf : X → Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) (hd : Gamma7Data K D Hf) :
    sigmaFam D Hf ≤ Subgroup.normalizer (K : Set X) ∧
      sigmaFam D Hf ≤ sigma0 K D Hf ⊔ Subgroup.centralizer (K : Set X) := by
  have hloc : ∀ d ∈ D, d ≠ 1 → Hf d ≤ Subgroup.normalizer (K : Set X) ∧
      Hf d ≤ sigma0 K D Hf ⊔ Subgroup.centralizer (K : Set X) := by
    intro d hdD hd1
    rcases gamma7_local hA hM h1 e hd hdD hd1 with hc | ⟨hge, hle, hdN, c, hc3, hcc, hroot⟩
    · exact ⟨hc.trans (Subgroup.centralizer_le_normalizer _), hc.trans le_sup_right⟩
    · refine ⟨hle.trans (sup_le ((g7_rootOf_le d).trans Subgroup.le_normalizer)
        (Subgroup.centralizer_le_normalizer _)), hle.trans (sup_le_sup_right ?_ _)⟩
      calc rootOf K d ≤ Hf d ⊓ K := le_inf hge (g7_rootOf_le d)
        _ ≤ sigma0 K D Hf :=
          le_iSup_of_le d (le_iSup_of_le hdD (le_iSup_of_le hd1 le_rfl))
  constructor
  · exact iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 => (hloc d hdD hd1).1
  · exact iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 => (hloc d hdD hd1).2

theorem gamma7_sigma0_cases (hA : A7Facts) (hM : AltSixSevenCentre) (h1 : Input19_21_1)
    {K D : Subgroup X} {Hf : X → Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) (hd : Gamma7Data K D Hf) :
    sigma0 K D Hf = ⊥ ∨
      (∃ d ∈ D, d ≠ 1 ∧ sigma0 K D Hf = rootOf K d ∧ IsRootFour (imgA7 K (rootOf K d) e)) ∨
      imgA7 K (sigma0 K D Hf) e = ⊤ := by
  classical
  have hK3 := hd.o3
  have hfam := hd.fam
  have hle_sigma : ∀ d ∈ D, d ≠ 1 → Hf d ⊓ K ≤ sigma0 K D Hf := fun d hdD hd1 =>
    le_iSup_of_le d (le_iSup_of_le hdD (le_iSup_of_le hd1 le_rfl))
  by_cases hall : ∀ d ∈ D, d ≠ 1 → Hf d ≤ Subgroup.centralizer (K : Set X)
  · refine Or.inl (le_bot_iff.1 ?_)
    exact iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 =>
      (g7_inf_eq_bot hd hdD hd1 (hall d hdD hd1)).le
  push_neg at hall
  obtain ⟨d₀, hd₀D, hd₀1, hd₀C⟩ := hall
  by_cases hdis : ∃ (d₁ d₂ : X) (c₁ c₂ : ↥(alternatingGroup (Fin 7))), d₁ ∈ D ∧ d₁ ≠ 1 ∧ d₂ ∈ D ∧
      d₂ ≠ 1 ∧ ¬ Hf d₁ ≤ Subgroup.centralizer (K : Set X) ∧
      ¬ Hf d₂ ≤ Subgroup.centralizer (K : Set X) ∧ (c₁ : Equiv.Perm (Fin 7)).IsThreeCycle ∧
      (c₂ : Equiv.Perm (Fin 7)).IsThreeCycle ∧ ConjActsAs d₁ K e c₁ ∧ ConjActsAs d₂ K e c₂ ∧
      Disjoint (c₁ : Equiv.Perm (Fin 7)).support (c₂ : Equiv.Perm (Fin 7)).support
  · refine Or.inr (Or.inr ?_)
    obtain ⟨d₁, d₂, c₁, c₂, hd₁D, hd₁1, hd₂D, hd₂1, hn₁, hn₂, h3₁, h3₂, hc₁, hc₂, hdisj⟩ := hdis
    have hN₁ := (gamma7_local_le h1 e hd hd₁D hd₁1 hn₁).1
    have hN₂ := (gamma7_local_le h1 e hd hd₂D hd₂1 hn₂).1
    have hT₁ := imgA7_rootOf hd.comp hK3 e (g7_orderOf_eq_three hfam.elemAbelian hd₁D hd₁1) hN₁ hc₁
    have hT₂ := imgA7_rootOf hd.comp hK3 e (g7_orderOf_eq_three hfam.elemAbelian hd₂D hd₂1) hN₂ hc₂
    have h4 := hA.2.2.2 c₁ c₂ h3₁ h3₂ hdisj
    refine top_le_iff.1 ?_
    rw [← h4, ← hT₁, ← hT₂]
    refine sup_le (g7_imgA7_mono e ?_) (g7_imgA7_mono e ?_)
    · rw [← g7_inf_eq_root hA hM h1 e hd hd₁D hd₁1 hn₁]; exact hle_sigma d₁ hd₁D hd₁1
    · rw [← g7_inf_eq_root hA hM h1 e hd hd₂D hd₂1 hn₂]; exact hle_sigma d₂ hd₂D hd₂1
  · refine Or.inr (Or.inl ⟨d₀, hd₀D, hd₀1, ?_, (gamma7_local_le h1 e hd hd₀D hd₀1 hd₀C).2.2.1⟩)
    have hroot_eq : ∀ d ∈ D, d ≠ 1 → ¬ Hf d ≤ Subgroup.centralizer (K : Set X) →
        rootOf K d = rootOf K d₀ := by
      intro d hdD hd1 hnd
      obtain ⟨hN, ⟨c, hc3, hc⟩, -, -⟩ := gamma7_local_le h1 e hd hdD hd1 hnd
      obtain ⟨hN₀, ⟨c₀, hc₀3, hc₀⟩, -, -⟩ := gamma7_local_le h1 e hd hd₀D hd₀1 hd₀C
      have hcomm : d * d₀ = d₀ * d := g7_comm_of_mem hfam.elemAbelian hdD hd₀D
      have hcc : c * c₀ = c₀ * c := g7_conj_comm e hN hN₀ hcomm hc hc₀
      have hz₁ : c₀ ∈ Subgroup.zpowers c := by
        rcases hA.2.2.1 c c₀ hc3 hc₀3 hcc with h | h
        · exact h
        · exact absurd ⟨d, d₀, c, c₀, hdD, hd1, hd₀D, hd₀1, hnd, hd₀C, hc3, hc₀3, hc, hc₀, h⟩ hdis
      have hz₂ : c ∈ Subgroup.zpowers c₀ := by
        rcases hA.2.2.1 c₀ c hc₀3 hc3 hcc.symm with h | h
        · exact h
        · exact absurd ⟨d₀, d, c₀, c, hd₀D, hd₀1, hdD, hd1, hd₀C, hnd, hc₀3, hc3, hc₀, hc, h⟩ hdis
      have hcent : Subgroup.centralizer ({c} : Set ↥(alternatingGroup (Fin 7))) =
          Subgroup.centralizer ({c₀} : Set ↥(alternatingGroup (Fin 7))) :=
        le_antisymm (g7_centralizer_le hz₁) (g7_centralizer_le hz₂)
      have hT := imgA7_rootOf hd.comp hK3 e (g7_orderOf_eq_three hfam.elemAbelian hdD hd1) hN hc
      have hT₀ := imgA7_rootOf hd.comp hK3 e
        (g7_orderOf_eq_three hfam.elemAbelian hd₀D hd₀1) hN₀ hc₀
      have himg : imgA7 K (rootOf K d) e = imgA7 K (rootOf K d₀) e := by rw [hT, hT₀, hcent]
      have hone : ∀ d' d'' : X, imgA7 K (rootOf K d') e = imgA7 K (rootOf K d'') e →
          rootOf K d' ≤ rootOf K d'' := by
        intro d' d'' himg' x hx
        have hxK : x ∈ K := g7_rootOf_le d' hx
        have hm : g7Pi e ⟨x, hxK⟩ ∈ imgA7 K (rootOf K d'') e := by
          rw [← himg', g7_imgA7_eq]
          exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
        rw [g7_imgA7_eq] at hm
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hm
        have hyR : (y : X) ∈ rootOf K d'' := Subgroup.mem_subgroupOf.1 hy
        obtain ⟨i, hi⟩ := g7_exists_pow_of_mem_pCoreOf 2 _ hyR
        obtain ⟨j, hj⟩ := g7_exists_pow_of_mem_pCoreOf 2 _ hx
        have hcen : (y : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          have hz : g7Pi e (y⁻¹ * ⟨x, hxK⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
          have := (g7Pi_eq_one_iff e _).1 hz ⟨h, hh⟩
          exact congrArg Subtype.val this
        have := g7_two_elt_central hK3 y.2 hxK hcen hi hj
        rw [← this]
        exact hyR
      exact le_antisymm (hone d d₀ himg) (hone d₀ d himg.symm)
    apply le_antisymm
    · refine iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 => ?_
      by_cases hC : Hf d ≤ Subgroup.centralizer (K : Set X)
      · rw [g7_inf_eq_bot hd hdD hd1 hC]; exact bot_le
      · rw [g7_inf_eq_root hA hM h1 e hd hdD hd1 hC, hroot_eq d hdD hd1 hC]
    · rw [← g7_inf_eq_root hA hM h1 e hd hd₀D hd₀1 hd₀C]
      exact hle_sigma d₀ hd₀D hd₀1

theorem gamma7_sigma (hA : A7Facts) (hM : AltSixSevenCentre) (h1 : Input19_21_1)
    {K D : Subgroup X} {Hf : X → Subgroup X}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))) (hd : Gamma7Data K D Hf)
    (hne : ¬ pCoreOf 2 (sigmaFam D Hf) ≤ Subgroup.centralizer (K : Set X)) :
    Gamma7Concl K e D Hf := by
  have hK3 := hd.o3
  obtain ⟨hSigN, hSigle⟩ := gamma7_sigma_le hA hM h1 e hd
  have hsigS : sigma0 K D Hf ≤ sigmaFam D Hf :=
    iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 =>
      inf_le_left.trans (le_iSup_of_le d (le_iSup_of_le hdD (le_iSup_of_le hd1 le_rfl)))
  have hσK : sigma0 K D Hf ≤ K :=
    iSup_le fun d => iSup_le fun hdD => iSup_le fun hd1 => inf_le_right
  have hO2le : pCoreOf 2 (sigmaFam D Hf) ≤ sigmaFam D Hf := g7_pCoreOf_le 2 _
  rcases gamma7_sigma0_cases hA hM h1 e hd with h0 | ⟨d, hdD, hd1, hσ, hroot⟩ | htop
  · exfalso
    apply hne
    refine hO2le.trans (hSigle.trans ?_)
    rw [h0, bot_sup_eq]
  ·
    have hRp : IsPGroup 2 (sigma0 K D Hf) := hσ ▸ g7_rootOf_pgroup d
    have hcomm : ∀ y ∈ sigma0 K D Hf, ∀ z ∈ Subgroup.centralizer (K : Set X), y * z = z * y :=
      fun y hy z hz => Subgroup.mem_centralizer_iff.1 hz y (hσK hy)
    have hnorm : sigmaFam D Hf ≤ Subgroup.normalizer (sigma0 K D Hf : Set X) := by
      apply g7_le_normalizer_of_conj
      intro x hx y hy
      obtain ⟨r, hr, s, hs, rfl⟩ := (g7_mem_sup_of_commute hcomm).1 (hSigle hx)
      have hsy : s * y = y * s := (hcomm y hy s hs).symm
      have : r * s * y * (r * s)⁻¹ = r * y * r⁻¹ := by
        calc r * s * y * (r * s)⁻¹ = r * (s * y) * s⁻¹ * r⁻¹ := by group
          _ = r * (y * s) * s⁻¹ * r⁻¹ := by rw [hsy]
          _ = r * y * r⁻¹ := by group
      rw [this]
      exact (sigma0 K D Hf).mul_mem ((sigma0 K D Hf).mul_mem hr hy) ((sigma0 K D Hf).inv_mem hr)
    have hRN : sigma0 K D Hf ≤ pCoreOf 2 (sigmaFam D Hf) := g7_le_pCoreOf hsigS hnorm hRp
    unfold Gamma7Concl
    refine ⟨hSigN, sigma0 K D Hf, hσK, by rw [hσ]; exact hroot, ?_, hO2le.trans hSigle⟩
    apply le_antisymm
    · exact g7_inf_le_root hK3 hσK hRp (g7_isPGroup_pCoreOf 2 _) (hO2le.trans hSigle)
    · exact le_inf hRN hσK
  ·
    exfalso
    have hperf : commutator ↥K = ⊤ := hd.comp.2.2.1
    have hsurj : ∀ k : ↥K, ∃ s ∈ (sigma0 K D Hf).subgroupOf K, ∃ z : ↥K,
        (∀ h : ↥K, h * z = z * h) ∧ k = s * z := by
      intro k
      have hk : g7Pi e k ∈ ((sigma0 K D Hf).subgroupOf K).map (g7Pi e) := by
        rw [← g7_imgA7_eq, htop]; exact Subgroup.mem_top _
      obtain ⟨s, hs, hsk⟩ := Subgroup.mem_map.1 hk
      refine ⟨s, hs, s⁻¹ * k, ?_, by group⟩
      apply (g7Pi_eq_one_iff e _).1
      rw [map_mul, map_inv, hsk, inv_mul_cancel]
    have hcomm_le : commutator ↥K ≤ (sigma0 K D Hf).subgroupOf K := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨s₁, hs₁, z₁, hz₁, rfl⟩ := hsurj a
      obtain ⟨s₂, hs₂, z₂, hz₂, rfl⟩ := hsurj b
      rw [g7_comm_mul_central_left hz₁, g7_comm_mul_central_right hz₂, commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs₁ hs₂)
        (Subgroup.inv_mem _ hs₁)) (Subgroup.inv_mem _ hs₂)
    have hKσ : K ≤ sigma0 K D Hf := by
      intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ (sigma0 K D Hf).subgroupOf K := hcomm_le (hperf ▸ Subgroup.mem_top _)
      exact Subgroup.mem_subgroupOf.1 this
    have hKS : K ≤ sigmaFam D Hf := hKσ.trans hsigS
    have hVk : ((pCoreOf 2 (sigmaFam D Hf) ⊓ K).subgroupOf K).Normal := by
      refine ⟨fun v hv g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hv ⊢
      exact ⟨g7_conj_mem_pCoreOf 2 _ (hKS g.2) hv.1, (g * v * g⁻¹).2⟩
    have hmap := Subgroup.Normal.map hVk (QuotientGroup.mk' (Subgroup.center ↥K))
      (QuotientGroup.mk'_surjective _)
    haveI hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hd.comp.2.2.2
    haveI := hmap
    have hV1 : ∀ x ∈ pCoreOf 2 (sigmaFam D Hf) ⊓ K, x = 1 := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (((pCoreOf 2 (sigmaFam D Hf) ⊓ K).subgroupOf K).map
          (QuotientGroup.mk' (Subgroup.center ↥K))) with hbot | htop'
      · intro x hx
        have hv : (⟨x, hx.2⟩ : ↥K) ∈ (pCoreOf 2 (sigmaFam D Hf) ⊓ K).subgroupOf K := hx
        have hm : QuotientGroup.mk' (Subgroup.center ↥K) ⟨x, hx.2⟩ ∈
            ((pCoreOf 2 (sigmaFam D Hf) ⊓ K).subgroupOf K).map
              (QuotientGroup.mk' (Subgroup.center ↥K)) := Subgroup.mem_map_of_mem _ hv
        rw [hbot, Subgroup.mem_bot] at hm
        have hcen : ∀ h : ↥K, h * (⟨x, hx.2⟩ : ↥K) = ⟨x, hx.2⟩ * h :=
          Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff _).1 hm)
        obtain ⟨j, hj⟩ := g7_exists_pow_of_mem_pCoreOf 2 _ hx.1
        have := g7_center_two_pow hK3 hcen (j := j) (Subtype.ext (by simpa using hj))
        exact congrArg Subtype.val this
      · exfalso
        apply g7_not_isPGroup_alt7
        intro a
        obtain ⟨y, rfl⟩ := e.surjective a
        have hy : y ∈ ((pCoreOf 2 (sigmaFam D Hf) ⊓ K).subgroupOf K).map
            (QuotientGroup.mk' (Subgroup.center ↥K)) := htop' ▸ Subgroup.mem_top y
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
        obtain ⟨j, hj⟩ := g7_exists_pow_of_mem_pCoreOf 2 _ (Subgroup.mem_subgroupOf.1 hv).1
        refine ⟨j, ?_⟩
        have hvj : v ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj)
        rw [← map_pow, ← map_pow, hvj, map_one, map_one]
    apply hne
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hnS : n ∈ sigmaFam D Hf := hO2le hn
    have hnN : n ∈ Subgroup.normalizer (K : Set X) := hSigN hnS
    have hkS : k ∈ sigmaFam D Hf := hKS hk
    have hmem : n * k * n⁻¹ * k⁻¹ ∈ pCoreOf 2 (sigmaFam D Hf) ⊓ K := by
      refine ⟨?_, ?_⟩
      · have h2 := (pCoreOf 2 (sigmaFam D Hf)).mul_mem hn
          (g7_conj_mem_pCoreOf 2 _ hkS ((pCoreOf 2 (sigmaFam D Hf)).inv_mem hn))
        simpa [mul_assoc] using h2
      · exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 hnN k).1 hk) (K.inv_mem hk)
    have h3 := hV1 _ hmem
    have h4 : n * k * n⁻¹ = k := mul_inv_eq_one.1 h3
    exact (mul_inv_eq_iff_eq_mul.1 h4).symm

end Gamma7Leaves

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
