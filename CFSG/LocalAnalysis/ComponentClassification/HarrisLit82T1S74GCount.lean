module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GFrat
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F4Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GComp
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

theorem map_conj_centralizer {G : Type*} [Group G] (n a : G) :
    (centralizer ({a} : Set G)).map (MulAut.conj n).toMonoidHom =
      centralizer ({n * a * n⁻¹} : Set G) := by
  have h := map_conj_inf_centralizer (C := ⊤) (mem_top n) a
  simpa using h

theorem map_conj_inf {G : Type*} [Group G] (n a b : G) :
    (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)).map (MulAut.conj n).toMonoidHom =
      centralizer ({n * a * n⁻¹} : Set G) ⊓ centralizer ({n * b * n⁻¹} : Set G) := by
  rw [map_inf_eq _ _ _ (MulAut.conj n).injective, map_conj_centralizer, map_conj_centralizer]

theorem card_centralizer_conj {G : Type*} [Group G] (g a : G) :
    Nat.card ↥(centralizer ({g * a * g⁻¹} : Set G)) = Nat.card ↥(centralizer ({a} : Set G)) := by
  rw [← map_conj_centralizer, card_map_of_injective (MulAut.conj g).injective]

namespace Setup

variable {G : Type} [Group G] [Finite G] (S : Setup G)

theorem exists_mul_D {h : G} (hh : h ∈ S.H) : ∃ l ∈ S.L, ∃ d ∈ S.D, h = l * d := by
  have hDN : S.D ≤ normalizer (S.L : Set G) := le_normalizer_of_conj_mem S.hLn inf_le_left
  have h1 : h ∈ ((S.L ⊔ S.D : Subgroup G) : Set G) := S.le_sup_D hh
  rw [coe_mul_of_right_le_normalizer_left S.L S.D hDN] at h1
  obtain ⟨l, hl, d, hd, rfl⟩ := h1
  exact ⟨l, hl, d, hd, rfl⟩

theorem exists_conj_of_J₂ (hSF : SpinFacts S.K S.p) {y y' : S.X} (hy : y ∈ spinJ₂ S.K)
    (hy' : y' ∈ spinJ₂ S.K) (hy1 : y ≠ 1) (hy'1 : y' ≠ 1) (hyp : y ^ S.p = 1)
    (hy'p : y' ^ S.p = 1) : ∃ g : S.X, g * y * g⁻¹ = y' := by
  obtain ⟨a, ha⟩ := hSF.conj_qOne y (Or.inl hy) hy1 hyp
  obtain ⟨b, hb⟩ := hSF.conj_qOne y' (Or.inl hy') hy'1 hy'p
  refine ⟨b⁻¹ * a, ?_⟩
  calc b⁻¹ * a * y * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * y * a⁻¹) * b := by group
    _ = b⁻¹ * (b * y' * b⁻¹) * b := by rw [ha, hb]
    _ = y' := by group

theorem card_Y_t (hF2b : F2b) (hSF : SpinFacts S.K S.p) :
    Nat.card S.H * (Nat.card S.K ^ 9 * (Nat.card S.K ^ 2 - 1) ^ 2) ≤
      Nat.card ↥(S.Y ⊓ centralizer ({S.t} : Set G)) * Nat.card S.L := by
  obtain ⟨n, hn1, hn2⟩ := S.exists_swap
  obtain ⟨hJ12, -, -⟩ := S.map_conj_swap hn1 hn2
  have hyJ : n * S.q₃ * n⁻¹ ∈ (spinJ₂ S.K).map S.φ := by
    rw [← hJ12]
    exact ⟨S.q₃, ⟨qThree S.K, ⟨_, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨y', hy'J, hy'⟩ := hyJ
  have hy'1 : y' ≠ 1 := by
    intro h
    apply hSF.qThree_ne_one
    apply S.hφ
    rw [map_one]
    calc S.q₃ = n⁻¹ * (n * S.q₃ * n⁻¹) * n := by group
      _ = 1 := by rw [← hy', h, map_one]; group
  have hy'p : y' ^ S.p = 1 := S.hφ (by
    rw [map_pow, hy', map_one]
    calc (n * S.q₃ * n⁻¹) ^ S.p = n * S.q₃ ^ S.p * n⁻¹ := by
          rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
      _ = 1 := by rw [← map_pow, hSF.qThree_pow, map_one]; group)
  have hcard1 : Nat.card ↥(S.Y ⊓ centralizer ({S.t} : Set G)) =
      Nat.card ↥(S.H ⊓ centralizer ({n * S.q₃ * n⁻¹} : Set G)) := by
    rw [← card_map_of_injective (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective,
      map_conj_inf, hn1, inf_comm]
  have hfr : ∀ h ∈ S.H, ∃ l ∈ S.L, h * (n * S.q₃ * n⁻¹) * h⁻¹ = l * (n * S.q₃ * n⁻¹) * l⁻¹ := by
    intro h hh
    obtain ⟨l₀, hl₀, d, hd, rfl⟩ := S.exists_mul_D hh
    have hdJ : d * (n * S.q₃ * n⁻¹) * d⁻¹ ∈ (spinJ₂ S.K).map S.φ := by
      rw [← S.map_conj_J_of_mem_D hd (Or.inr (Or.inl rfl))]
      exact ⟨_, ⟨y', hy'J, hy'⟩, rfl⟩
    obtain ⟨y'', hy''J, hy''⟩ := hdJ
    have hy''1 : y'' ≠ 1 := by
      intro h
      apply hy'1
      apply S.hφ
      rw [hy', map_one]
      calc n * S.q₃ * n⁻¹ = d⁻¹ * (d * (n * S.q₃ * n⁻¹) * d⁻¹) * d := by group
        _ = 1 := by rw [← hy'', h, map_one]; group
    have hy''p : y'' ^ S.p = 1 := S.hφ (by
      rw [map_pow, hy'', map_one]
      calc (d * (n * S.q₃ * n⁻¹) * d⁻¹) ^ S.p = d * (n * S.q₃ * n⁻¹) ^ S.p * d⁻¹ := by
            rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
        _ = 1 := by rw [← hy', ← map_pow, hy'p, map_one]; group)
    obtain ⟨g, hg⟩ := S.exists_conj_of_J₂ hSF hy'J hy''J hy'1 hy''1 hy'p hy''p
    refine ⟨l₀ * S.φ g, mul_mem hl₀ (S.mem_L g), ?_⟩
    calc l₀ * d * (n * S.q₃ * n⁻¹) * (l₀ * d)⁻¹ = l₀ * (d * (n * S.q₃ * n⁻¹) * d⁻¹) * l₀⁻¹ := by
          group
      _ = l₀ * S.φ (g * y' * g⁻¹) * l₀⁻¹ := by rw [hg, hy'']
      _ = l₀ * S.φ g * (n * S.q₃ * n⁻¹) * (l₀ * S.φ g)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hy']; group
  have heq := card_inf_mul_card_eq S.hLH S.hLn (le_sup_inf_centralizer hfr S.hLH)
  have hcard2 : Nat.card ↥(S.L ⊓ centralizer ({n * S.q₃ * n⁻¹} : Set G)) =
      Nat.card ↥(centralizer ({qOne S.K} : Set S.X)) := by
    rw [← hy', S.card_inf_centralizer]
    obtain ⟨g, hg⟩ := hSF.conj_qOne y' (Or.inl hy'J) hy'1 hy'p
    rw [← hg, card_centralizer_conj]
  have hF := hF2b S.K S.odd_card (S.hK ▸ S.h5)
  rw [hcard1, heq, hcard2]
  exact Nat.mul_le_mul_left _ hF

theorem card_M_t (hSF : SpinFacts S.K S.p) :
    Nat.card ↥(S.M ⊓ centralizer ({S.t} : Set G)) * Nat.card S.L ≤
      Nat.card S.H * (Nat.card S.K ^ 3 * (Nat.card S.K ^ 2 - 1) ^ 2) := by
  have hle : S.M ⊓ centralizer ({S.t} : Set G) ≤ S.H ⊓ (S.Y ⊓ centralizer ({S.t} : Set G)) :=
    fun x hx => mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).1).2,
      mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp (mem_inf.mp hx).1).1).1, (mem_inf.mp hx).2⟩⟩
  have h1 := card_le_of_le hle
  have h2 := card_inf_mul_card_le (C := S.Y ⊓ centralizer ({S.t} : Set G)) S.hLH S.hLn
  have hLYt : S.L ⊓ (S.Y ⊓ centralizer ({S.t} : Set G)) =
      (centralizer ({tSeven S.K} : Set S.X) ⊓ centralizer ({qThree S.K} : Set S.X)).map S.φ := by
    rw [S.map_inf, S.map_centralizer, S.map_centralizer]
    ext x
    simp only [mem_inf]
    tauto
  have h3 : Nat.card ↥(S.L ⊓ (S.Y ⊓ centralizer ({S.t} : Set G))) ≤
      Nat.card S.K ^ 3 * (Nat.card S.K ^ 2 - 1) ^ 2 := by
    rw [hLYt, S.card_map]
    exact hSF.card_centralizer_tSeven_qThree
  calc Nat.card ↥(S.M ⊓ centralizer ({S.t} : Set G)) * Nat.card S.L ≤
      Nat.card ↥(S.H ⊓ (S.Y ⊓ centralizer ({S.t} : Set G))) * Nat.card S.L :=
        Nat.mul_le_mul_right _ h1
    _ ≤ Nat.card S.H * Nat.card ↥(S.L ⊓ (S.Y ⊓ centralizer ({S.t} : Set G))) := h2
    _ ≤ _ := Nat.mul_le_mul_left _ h3

variable {iX : S.X} {S₀ B : Subgroup S.X}

theorem q₃_facts : S.q₃ * S.t = S.t * S.q₃ ∧ S.q₃ * S.z = S.z * S.q₃ := by
  have h := (spinJ_le_centralizer S.hp S.hp2 S.hK).1 (⟨_, rfl⟩ : qThree S.K ∈ spinJ₁ S.K)
  rw [mem_centralizer_singleton_iff] at h
  exact ⟨by rw [← map_mul, ← map_mul, h], S.commute_z (S.mem_L _)⟩

theorem mem_M (hI : IBarFacts S.K S.p iX) :
    S.z ∈ S.M ∧ S.t ∈ S.M ∧ S.iG iX ∈ S.M := by
  obtain ⟨-, hiY, hit, hiz, hiL⟩ := S.iG_facts hI
  obtain ⟨hzz, -, htt, -, hzt, -⟩ := S.facts
  obtain ⟨hqt, hqz⟩ := S.q₃_facts
  refine ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hqz.symm,
      S.mem_normalizer_T_of_commute rfl hzt⟩, mem_centralizer_singleton_iff.mpr rfl⟩,
    mem_inf.mpr ⟨mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hqt.symm,
      S.mem_normalizer_T_of_commute hzt.symm rfl⟩, mem_centralizer_singleton_iff.mpr hzt.symm⟩,
    mem_inf.mpr ⟨mem_inf.mpr ⟨hiY, S.mem_normalizer_T ?_ ?_⟩, S.hLH hiL⟩⟩
  · rw [hiz, mul_inv_cancel_right]
    exact S.z_mem_T
  · rw [hit]
    exact mul_mem S.z_mem_T S.t_mem_T

theorem card_M_i (hSF : SpinFacts S.K S.p) (hI : IBarFacts S.K S.p iX) :
    Nat.card S.H * (2 * Nat.card S.K ^ 2 * (Nat.card S.K ^ 2 - 1)) ≤
      Nat.card ↥(S.M ⊓ centralizer ({S.iG iX} : Set G)) * Nat.card S.L := by
  obtain ⟨hii, hiY, hit, hiz, hiL⟩ := S.iG_facts hI
  obtain ⟨hzz, hz1, htt, ht1, hzt, hzt', -⟩ := S.facts
  have hMH : S.M ≤ S.H := inf_le_right
  have hfrD : ∀ d ∈ S.D, ∃ c ∈ S.L ⊓ S.D, d * S.q₃ * d⁻¹ = c * S.q₃ * c⁻¹ := by
    intro d hd
    have hdJ : d * S.q₃ * d⁻¹ ∈ (spinJ₁ S.K).map S.φ := by
      rw [← S.map_conj_J_of_mem_D hd (Or.inl rfl)]
      exact ⟨S.q₃, ⟨qThree S.K, ⟨_, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨y, hyJ, hy⟩ := hdJ
    have hy1 : y ≠ 1 := by
      intro h
      apply hSF.qThree_ne_one
      apply S.hφ
      rw [map_one]
      calc S.q₃ = d⁻¹ * (d * S.q₃ * d⁻¹) * d := by group
        _ = 1 := by rw [← hy, h, map_one]; group
    have hyp : y ^ S.p = 1 := S.hφ (by
      rw [map_pow, hy, map_one]
      calc (d * S.q₃ * d⁻¹) ^ S.p = d * S.q₃ ^ S.p * d⁻¹ := by
            rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
        _ = 1 := by rw [← map_pow, hSF.qThree_pow, map_one]; group)
    obtain ⟨g, hgt, hg⟩ := hSF.conj_qThree y hyJ hy1 hyp
    have hgD : S.φ g⁻¹ ∈ S.L ⊓ S.D := by
      have h1 := (S.map_centralizer (tSeven S.K)).le ⟨g⁻¹, inv_mem hgt, rfl⟩
      exact mem_inf.mpr ⟨(mem_inf.mp h1).1, mem_inf.mpr ⟨S.hLH (mem_inf.mp h1).1,
        (mem_inf.mp h1).2⟩⟩
    refine ⟨S.φ g⁻¹, hgD, ?_⟩
    have hy' : y = g⁻¹ * qThree S.K * g := by rw [← hg]; group
    rw [← hy, hy']
    simp only [map_mul, map_inv, inv_inv]
  have hHLM : S.H ≤ S.L ⊔ S.M := by
    intro h hh
    obtain ⟨l₀, hl₀, d, hd, rfl⟩ := S.exists_mul_D hh
    obtain ⟨c, hc, hcd⟩ := hfrD d hd
    have hcdD : c⁻¹ * d ∈ S.D := mul_mem (inv_mem (mem_inf.mp hc).2) hd
    have hcdq : c⁻¹ * d ∈ S.Y := by
      rw [mem_centralizer_singleton_iff]
      calc c⁻¹ * d * S.q₃ = c⁻¹ * (d * S.q₃ * d⁻¹) * d := by group
        _ = c⁻¹ * (c * S.q₃ * c⁻¹) * d := by rw [hcd]
        _ = S.q₃ * (c⁻¹ * d) := by group
    have hcdM : c⁻¹ * d ∈ S.M := mem_inf.mpr ⟨mem_inf.mpr ⟨hcdq,
      S.mem_normalizer_T_of_commute (mem_centralizer_singleton_iff.mp (mem_inf.mp hcdD).1)
        (mem_centralizer_singleton_iff.mp (mem_inf.mp hcdD).2)⟩, (mem_inf.mp hcdD).1⟩
    have : l₀ * d = (l₀ * c) * (c⁻¹ * d) := by group
    rw [this]
    exact mul_mem_sup (mul_mem hl₀ (mem_inf.mp hc).1) hcdM
  have e1 := card_inf_mul_card_eq (C := S.M) S.hLH S.hLn
    (by rw [inf_of_le_right hMH]; exact hHLM)
  rw [inf_of_le_right hMH] at e1
  have hLMn : ∀ m ∈ S.M, ∀ x ∈ S.L ⊓ S.M, m * x * m⁻¹ ∈ S.L ⊓ S.M := fun m hm x hx =>
    mem_inf.mpr ⟨S.hLn m (hMH hm) x (mem_inf.mp hx).1,
      mul_mem (mul_mem hm (mem_inf.mp hx).2) (inv_mem hm)⟩
  have hiM := (S.mem_M hI).2.2
  have hfrM : ∀ m ∈ S.M, ∃ w ∈ S.L ⊓ S.M, m * S.iG iX * m⁻¹ = w * S.iG iX * w⁻¹ := by
    intro m hm
    have hu : m * S.iG iX * m⁻¹ ∈ S.L ⊓ S.M := hLMn m hm _ (mem_inf.mpr ⟨hiL, hiM⟩)
    obtain ⟨w', hw'⟩ := S.exists_eq_of_mem_L (mem_inf.mp hu).1
    have huM := (mem_inf.mp hu).2
    have hw'q : w' ∈ centralizer ({qThree S.K} : Set S.X) := by
      have h1 : S.φ w' ∈ S.L ⊓ S.Y := mem_inf.mpr ⟨S.mem_L w',
        hw' ▸ (mem_inf.mp (mem_inf.mp huM).1).1⟩
      rw [S.L_inf_Y] at h1
      obtain ⟨w'', hw'', hw''w⟩ := h1
      rw [← S.hφ hw''w]
      exact hw''
    have hw'N : w' ∈ normalizer (fourT S.K : Set S.X) := by
      have h1 := S.le_map_normalizer (mem_inf.mpr ⟨S.mem_L w',
        hw' ▸ (mem_inf.mp (mem_inf.mp huM).1).2⟩)
      obtain ⟨w'', hw'', hw''w⟩ := h1
      rw [← S.hφ hw''w]
      exact hw''
    have hw'w' : w' * w' = 1 := S.hφ (by
      rw [map_mul, hw', map_one]
      calc m * S.iG iX * m⁻¹ * (m * S.iG iX * m⁻¹) = m * (S.iG iX * S.iG iX) * m⁻¹ := by group
        _ = 1 := by rw [hii]; group)
    have hw't : w' * tSeven S.K ≠ tSeven S.K * w' := by
      intro hc
      have hc' : m * S.iG iX * m⁻¹ * S.t = S.t * (m * S.iG iX * m⁻¹) := by
        rw [← hw', ← map_mul, ← map_mul, hc]
      have hmN : m⁻¹ ∈ normalizer (S.T : Set G) :=
        inv_mem (mem_inf.mp (mem_inf.mp hm).1).2
      have hci : S.iG iX * (m⁻¹ * S.t * m) = (m⁻¹ * S.t * m) * S.iG iX := by
        calc S.iG iX * (m⁻¹ * S.t * m) = m⁻¹ * (m * S.iG iX * m⁻¹ * S.t) * m := by group
          _ = m⁻¹ * (S.t * (m * S.iG iX * m⁻¹)) * m := by rw [hc']
          _ = (m⁻¹ * S.t * m) * S.iG iX := by group
      have hcit : S.iG iX * S.t = S.t * S.iG iX := by
        rcases S.conj_t_of_mem_normalizer (inv_mem (hMH hm)) hmN with h | h <;>
          rw [inv_inv] at h <;> rw [h] at hci
        · exact hci
        · calc S.iG iX * S.t = S.z⁻¹ * (S.z * S.iG iX) * S.t := by group
            _ = S.z⁻¹ * (S.iG iX * S.z) * S.t := by rw [hiz]
            _ = S.z⁻¹ * (S.iG iX * (S.z * S.t)) := by group
            _ = S.z⁻¹ * ((S.z * S.t) * S.iG iX) := by rw [hci]
            _ = S.t * S.iG iX := by group
      apply hz1
      have h1 : S.iG iX * S.t * (S.iG iX)⁻¹ = S.t := by rw [hcit]; group
      rw [hit] at h1
      calc S.z = S.z * S.t * (S.t)⁻¹ := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨m', hm', hm'i⟩ := hI.conj_M w' (mem_inf.mpr ⟨hw'q, hw'N⟩) hw'w' hw't
    have hm'G : S.φ m' ∈ S.L ⊓ S.M := by
      have h1 := (S.map_centralizer (qThree S.K)).le ⟨m', (mem_inf.mp hm').1, rfl⟩
      exact mem_inf.mpr ⟨S.mem_L m', mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp h1).2,
        S.map_normalizer_le ⟨m', (mem_inf.mp hm').2, rfl⟩⟩, S.hLH (S.mem_L m')⟩⟩
    refine ⟨S.φ m', hm'G, ?_⟩
    rw [← hw', ← hm'i]
    simp only [map_mul, map_inv]
  have e2 := card_inf_mul_card_eq (H := S.M) (L := S.L ⊓ S.M)
    (C := centralizer ({S.iG iX} : Set G)) inf_le_right hLMn
    (le_sup_inf_centralizer hfrM inf_le_right)
  have hlow : 2 * Nat.card S.K ^ 2 * (Nat.card S.K ^ 2 - 1) ≤
      Nat.card ↥(S.L ⊓ S.M ⊓ centralizer ({S.iG iX} : Set G)) := by
    refine hI.card_M.trans ?_
    rw [← S.card_map]
    refine card_le_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxqN, hxi⟩ := mem_inf.mp hx
    obtain ⟨hxq, hxN⟩ := mem_inf.mp hxqN
    have h1 := (S.map_centralizer (qThree S.K)).le ⟨x, hxq, rfl⟩
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨S.mem_L x, mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp h1).2,
      S.map_normalizer_le ⟨x, hxN, rfl⟩⟩, S.hLH (S.mem_L x)⟩⟩, ?_⟩
    rw [mem_centralizer_singleton_iff] at hxi ⊢
    rw [← map_mul, ← map_mul, hxi]
  have hpos : 0 < Nat.card ↥(S.L ⊓ S.M) := Nat.card_pos
  have key : Nat.card ↥(S.M ⊓ centralizer ({S.iG iX} : Set G)) * Nat.card S.L =
      Nat.card S.H * Nat.card ↥(S.L ⊓ S.M ⊓ centralizer ({S.iG iX} : Set G)) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card ↥(S.M ⊓ centralizer ({S.iG iX} : Set G)) * Nat.card S.L *
          Nat.card ↥(S.L ⊓ S.M) =
        Nat.card ↥(S.M ⊓ centralizer ({S.iG iX} : Set G)) * Nat.card ↥(S.L ⊓ S.M) *
          Nat.card S.L := by ring
      _ = Nat.card S.M * Nat.card ↥(S.L ⊓ S.M ⊓ centralizer ({S.iG iX} : Set G)) *
          Nat.card S.L := by rw [e2]
      _ = Nat.card S.M * Nat.card S.L *
          Nat.card ↥(S.L ⊓ S.M ⊓ centralizer ({S.iG iX} : Set G)) := by ring
      _ = Nat.card S.H * Nat.card ↥(S.L ⊓ S.M) *
          Nat.card ↥(S.L ⊓ S.M ⊓ centralizer ({S.iG iX} : Set G)) := by rw [e1]
      _ = Nat.card S.H * Nat.card ↥(S.L ⊓ S.M ⊓ centralizer ({S.iG iX} : Set G)) *
          Nat.card ↥(S.L ⊓ S.M) := by ring
  rw [key]
  exact Nat.mul_le_mul_left _ hlow

theorem iX_facts (hI : IBarFacts S.K S.p iX) :
    iX ≠ 1 ∧ iX * tSeven S.K ≠ tSeven S.K * iX := by
  obtain ⟨-, hz1, -⟩ := spinZ_facts S.hp S.hp2 S.hK
  have key : iX * tSeven S.K ≠ tSeven S.K * iX := by
    intro h
    have hct := hI.conj_t
    rw [h, mul_inv_cancel_right] at hct
    apply hz1
    calc spinZ S.K = spinZ S.K * tSeven S.K * (tSeven S.K)⁻¹ := by group
      _ = 1 := by rw [← hct]; group
  refine ⟨fun h => key (by rw [h, one_mul, mul_one]), key⟩

theorem card_Y_i (hSF : SpinFacts S.K S.p) (hI : IBarFacts S.K S.p iX) :
    Nat.card ↥(S.Y ⊓ centralizer ({S.iG iX} : Set G)) * Nat.card S.L ≤
      Nat.card S.H * (4 * Nat.card S.K ^ 7 * (Nat.card S.K ^ 2 - 1)) := by
  obtain ⟨hi1, hit⟩ := S.iX_facts hI
  have hi2 : orderOf iX = 2 := orderOf_eq_prime (by rw [pow_two]; exact hI.mul_self) hi1
  have hiZ : iX ∉ center S.X := fun h => hit ((mem_center_iff.mp h (tSeven S.K)).symm)
  obtain ⟨lX, hlX⟩ := spinSeven_lemma410b S.odd_card S.four_le_card hi2 hiZ
  obtain ⟨a, haJ, b, hbJ, ha1, hb1, hap, hbp, hab⟩ := hI.shape lX hlX
  obtain ⟨n, hn1, hn2⟩ := S.exists_swap
  obtain ⟨-, hJ21, hJ33⟩ := S.map_conj_swap hn1 hn2
  set g₂ := n * (S.φ lX)⁻¹ with hg₂
  have hg₂i : g₂ * S.iG iX * g₂⁻¹ = S.z := by
    have h1 : (S.φ lX)⁻¹ * S.iG iX * S.φ lX = S.t := by
      rw [← hlX]
      simp only [map_mul, map_inv]
      group
    calc g₂ * S.iG iX * g₂⁻¹ = n * ((S.φ lX)⁻¹ * S.iG iX * S.φ lX) * n⁻¹ := by rw [hg₂]; group
      _ = S.z := by rw [h1, hn1]
  have hx₂ : g₂ * S.q₃ * g₂⁻¹ = (n * S.φ a * n⁻¹) * (n * S.φ b * n⁻¹) := by
    have h1 : (S.φ lX)⁻¹ * S.q₃ * S.φ lX = S.φ a * S.φ b := by
      rw [← map_mul, ← hab]
      simp only [map_mul, map_inv]
    calc g₂ * S.q₃ * g₂⁻¹ = n * ((S.φ lX)⁻¹ * S.q₃ * S.φ lX) * n⁻¹ := by rw [hg₂]; group
      _ = n * (S.φ a * S.φ b) * n⁻¹ := by rw [h1]
      _ = (n * S.φ a * n⁻¹) * (n * S.φ b * n⁻¹) := by group
  have ha' : n * S.φ a * n⁻¹ ∈ (spinJ₁ S.K).map S.φ := by
    rw [← hJ21]
    exact ⟨_, ⟨a, haJ, rfl⟩, rfl⟩
  have hb' : n * S.φ b * n⁻¹ ∈ (spinJ₃ S.K).map S.φ := by
    rw [← hJ33]
    exact ⟨_, ⟨b, hbJ, rfl⟩, rfl⟩
  obtain ⟨a', ha'J, ha'a⟩ := ha'
  obtain ⟨b', hb'J, hb'b⟩ := hb'
  have hconj1 : ∀ c : S.X, c ≠ 1 → c ^ S.p = 1 → ∀ c' : S.X, S.φ c' = n * S.φ c * n⁻¹ →
      c' ≠ 1 ∧ c' ^ S.p = 1 := by
    intro c hc1 hcp c' hc'
    refine ⟨fun h => hc1 (S.hφ ?_), S.hφ ?_⟩
    · rw [map_one]
      calc S.φ c = n⁻¹ * (n * S.φ c * n⁻¹) * n := by group
        _ = 1 := by rw [← hc', h, map_one]; group
    · rw [map_pow, hc', map_one]
      calc (n * S.φ c * n⁻¹) ^ S.p = n * S.φ c ^ S.p * n⁻¹ := by
            rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
        _ = 1 := by rw [← map_pow, hcp, map_one]; group
  obtain ⟨ha'1, ha'p⟩ := hconj1 a ha1 hap a' ha'a
  obtain ⟨hb'1, hb'p⟩ := hconj1 b hb1 hbp b' hb'b
  have hcard1 : Nat.card ↥(S.Y ⊓ centralizer ({S.iG iX} : Set G)) =
      Nat.card ↥(S.H ⊓ centralizer ({S.φ (a' * b')} : Set G)) := by
    rw [← card_map_of_injective (f := (MulAut.conj g₂).toMonoidHom) (MulAut.conj g₂).injective,
      map_conj_inf, hg₂i, hx₂, ← ha'a, ← hb'b, ← map_mul, inf_comm]
  rw [hcard1]
  calc Nat.card ↥(S.H ⊓ centralizer ({S.φ (a' * b')} : Set G)) * Nat.card S.L ≤
      Nat.card S.H * Nat.card ↥(S.L ⊓ centralizer ({S.φ (a' * b')} : Set G)) :=
        card_inf_mul_card_le S.hLH S.hLn
    _ ≤ _ := by
        refine Nat.mul_le_mul_left _ ?_
        rw [S.card_inf_centralizer]
        exact hSF.card_centralizer_mul a' ha'J b' (Or.inr hb'J) ha'1 hb'1 ha'p hb'p

theorem count (hF1 : F1) (hI : IBarFacts S.K S.p iX) (hSy : SylowFacts S.K iX S₀ B) :
    Nat.card ↥(S.Y ⊓ centralizer ({S.t} : Set G)) *
        Nat.card ↥(S.M ⊓ centralizer ({S.iG iX} : Set G)) ≤
      Nat.card ↥(S.Y ⊓ centralizer ({S.iG iX} : Set G)) *
        Nat.card ↥(S.M ⊓ centralizer ({S.t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hii, -, hit, hiz, -⟩ := S.iG_facts hI
  obtain ⟨hzz, hz1, htt, ht1, hzt, hzt', -⟩ := S.facts
  obtain ⟨hzM, htM, hiM⟩ := S.mem_M hI
  have hi1 : S.iG iX ≠ 1 := fun h => (S.iX_facts hI).1 (S.hφ (h.trans (map_one S.φ).symm))
  have hKY : (pPrimeCore 2 ↥S.Y).map S.Y.subtype ≤ S.Y := map_subtype_le _
  have hKn : ∀ y ∈ S.Y, ∀ k ∈ (pPrimeCore 2 ↥S.Y).map S.Y.subtype,
      y * k * y⁻¹ ∈ (pPrimeCore 2 ↥S.Y).map S.Y.subtype := fun y hy k hk =>
    CFSG.Walter.conj_mem_map_of_characteristic (le_normalizer hy) hk
  have hodd : Odd (Nat.card ↥((pPrimeCore 2 ↥S.Y).map S.Y.subtype)) := by
    rw [card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hKT : (pPrimeCore 2 ↥S.Y).map S.Y.subtype ⊓ centralizer ({S.z, S.t} : Set G) ≤ S.M := by
    intro x hx
    obtain ⟨hxK, hxC⟩ := mem_inf.mp hx
    have hxz : x * S.z = S.z * x := (mem_centralizer_iff.mp hxC S.z (Set.mem_insert _ _)).symm
    have hxt : x * S.t = S.t * x :=
      (mem_centralizer_iff.mp hxC S.t (Set.mem_insert_of_mem _ rfl)).symm
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hKY hxK, S.mem_normalizer_T_of_commute hxz hxt⟩,
      mem_centralizer_singleton_iff.mpr hxz⟩
  have hti : S.t * S.iG iX * S.t⁻¹ = S.z * S.iG iX := by
    calc S.t * S.iG iX * S.t⁻¹ = S.t * (S.iG iX * S.t * (S.iG iX)⁻¹)⁻¹ * S.iG iX := by group
      _ = S.t * (S.z * S.t)⁻¹ * S.iG iX := by rw [hit]
      _ = S.z⁻¹ * S.iG iX := by group
      _ = S.z * S.iG iX := by rw [inv_eq_of_mul_eq_one_right hzz]
  exact card_mul_card_le_of_brauerWielandt hKY hKn hodd (inf_le_left.trans inf_le_left)
    (S.le_K_sup_M hF1 hI hSy) inf_le_right hzz htt hii hz1 ht1 hi1 hzt'
    (S.iG_ne_z hI).symm hzM htM hiM hKT ⟨S.iG iX, hiM, hit⟩ ⟨S.t, htM, hti⟩

theorem false_of_spinFacts (hF1 : F1) (hF2b : F2b) (hSF : SpinFacts S.K S.p) : False := by
  obtain ⟨iX, hI⟩ := hSF.iBar
  obtain ⟨S₀, B, hSy⟩ := hI.sylow
  have hc := S.count hF1 hI hSy
  have ha := S.card_Y_t hF2b hSF
  have hb := S.card_M_i hSF hI
  have hc' := S.card_Y_i hSF hI
  have hd := S.card_M_t hSF
  have hq5 : 5 ≤ Nat.card S.K := S.hK ▸ S.h5
  set q := Nat.card S.K
  set yt := Nat.card ↥(S.Y ⊓ centralizer ({S.t} : Set G))
  set mi := Nat.card ↥(S.M ⊓ centralizer ({S.iG iX} : Set G))
  set yi := Nat.card ↥(S.Y ⊓ centralizer ({S.iG iX} : Set G))
  set mt := Nat.card ↥(S.M ⊓ centralizer ({S.t} : Set G))
  set Lc := Nat.card S.L
  set Hc := Nat.card S.H
  have hr : 0 < q ^ 2 - 1 := by
    have : 25 ≤ q ^ 2 := by nlinarith
    omega
  have hHc : 0 < Hc := Nat.card_pos
  have h1 : Hc * (q ^ 9 * (q ^ 2 - 1) ^ 2) * (Hc * (2 * q ^ 2 * (q ^ 2 - 1))) ≤
      Hc * (4 * q ^ 7 * (q ^ 2 - 1)) * (Hc * (q ^ 3 * (q ^ 2 - 1) ^ 2)) := by
    calc Hc * (q ^ 9 * (q ^ 2 - 1) ^ 2) * (Hc * (2 * q ^ 2 * (q ^ 2 - 1))) ≤
        (yt * Lc) * (mi * Lc) := Nat.mul_le_mul ha hb
      _ = (yt * mi) * (Lc * Lc) := by ring
      _ ≤ (yi * mt) * (Lc * Lc) := Nat.mul_le_mul_right _ hc
      _ = (yi * Lc) * (mt * Lc) := by ring
      _ ≤ Hc * (4 * q ^ 7 * (q ^ 2 - 1)) * (Hc * (q ^ 3 * (q ^ 2 - 1) ^ 2)) :=
          Nat.mul_le_mul hc' hd
  obtain ⟨r, hr'⟩ : ∃ r, r = q ^ 2 - 1 := ⟨_, rfl⟩
  rw [← hr'] at h1 hr
  have h2 : (q ^ 9 * r ^ 2) * (2 * q ^ 2 * r) ≤ (4 * q ^ 7 * r) * (q ^ 3 * r ^ 2) := by
    have hH2 : 0 < Hc * Hc := Nat.mul_pos hHc hHc
    have : ((q ^ 9 * r ^ 2) * (2 * q ^ 2 * r)) * (Hc * Hc) ≤
        ((4 * q ^ 7 * r) * (q ^ 3 * r ^ 2)) * (Hc * Hc) := by
      calc ((q ^ 9 * r ^ 2) * (2 * q ^ 2 * r)) * (Hc * Hc) =
          Hc * (q ^ 9 * r ^ 2) * (Hc * (2 * q ^ 2 * r)) := by ring
        _ ≤ Hc * (4 * q ^ 7 * r) * (Hc * (q ^ 3 * r ^ 2)) := h1
        _ = ((4 * q ^ 7 * r) * (q ^ 3 * r ^ 2)) * (Hc * Hc) := by ring
    exact Nat.le_of_mul_le_mul_right this hH2
  have h3 : q * (2 * q ^ 10 * r ^ 3) ≤ 2 * (2 * q ^ 10 * r ^ 3) := by
    calc q * (2 * q ^ 10 * r ^ 3) = (q ^ 9 * r ^ 2) * (2 * q ^ 2 * r) := by ring
      _ ≤ (4 * q ^ 7 * r) * (q ^ 3 * r ^ 2) := h2
      _ = 2 * (2 * q ^ 10 * r ^ 3) := by ring
  have hpos : 0 < 2 * q ^ 10 * r ^ 3 :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by omega) 10)) (pow_pos hr 3)
  have h4 := Nat.le_of_mul_le_mul_right h3 hpos
  omega

end Setup

end CFSG.ComponentClassification.HarrisLit.T1.S74
