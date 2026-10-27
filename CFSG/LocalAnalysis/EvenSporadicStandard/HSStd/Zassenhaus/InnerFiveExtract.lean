module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerConfig
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Types

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup Wreath

namespace InnerD8Config

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

theorem pow_five_of_mem_sup {f₀ f₁ : G} (hc : Commute f₀ f₁) (h0 : f₀ ^ 5 = 1)
    (h1 : f₁ ^ 5 = 1) {x : G} (hx : x ∈ zpowers f₀ ⊔ zpowers f₁) : x ^ 5 = 1 := by
  have key : ∃ i j : ℤ, x = f₀ ^ i * f₁ ^ j := by
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact ⟨i, 0, by simp⟩
      · exact ⟨0, j, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, j, rfl⟩ := hx
      obtain ⟨k, l, rfl⟩ := hy
      refine ⟨i + k, j + l, ?_⟩
      have h := (hc.zpow_zpow k j).eq
      calc f₀ ^ i * f₁ ^ j * (f₀ ^ k * f₁ ^ l) = f₀ ^ i * (f₁ ^ j * f₀ ^ k) * f₁ ^ l := by
            simp only [mul_assoc]
        _ = f₀ ^ i * (f₀ ^ k * f₁ ^ j) * f₁ ^ l := by rw [← h]
        _ = f₀ ^ (i + k) * f₁ ^ (j + l) := by rw [zpow_add, zpow_add]; simp only [mul_assoc]
    | inv x _ hx =>
      obtain ⟨i, j, rfl⟩ := hx
      refine ⟨-i, -j, ?_⟩
      rw [mul_inv_rev, zpow_neg, zpow_neg]
      exact ((hc.zpow_zpow i j).inv_inv).symm.eq.symm ▸ rfl
  obtain ⟨i, j, rfl⟩ := key
  have hp : ∀ (f : G) (n : ℤ), f ^ 5 = 1 → (f ^ n) ^ 5 = 1 := by
    intro f n hf
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hf, one_zpow]
  rw [(hc.zpow_zpow i j).mul_pow, hp _ _ h0, hp _ _ h1, one_mul]

theorem exists_swap (c : InnerD8Config L t) (hρ : c.rho.range = ⊤)
    (γ : MulAut (alternatingGroup (Fin 6))) :
    ∃ q : ↥c.P, c.rho q = base 1 γ ∧ (∀ k ∈ c.L₁, Commute (q : G) k) ∧
      ∀ y : ↥c.L₁, (t⁻¹ * (q : G) * t) * (y : G) * (t⁻¹ * (q : G) * t)⁻¹ =
        ((c.eL₁.symm (γ (c.eL₁ y)) : ↥c.L₁) : G) := by
  have hti : t⁻¹ = t := c.pair.t_inv
  have hmem : base 1 γ ∈ c.rho.range := hρ ▸ Subgroup.mem_top _
  obtain ⟨q, hq⟩ := hmem
  refine ⟨q, hq, ?_⟩
  set γ' := (MulAut.congr c.eL₁).symm γ with hγ'
  have hr : c.pair.rho q = base 1 γ' := by
    apply (mapEquiv (MulAut.congr c.eL₁)).injective
    rw [← c.rho_apply, hq, mapEquiv_base, map_one, hγ', MulEquiv.apply_symm_apply]
  have hbase : c.pair.rho q ∈ baseSubgroup := by
    rw [hr, mem_baseSubgroup_iff, swapChar_base]
  have hqn : (q : G) ∈ normalizer (c.L₁ : Set G) :=
    (mem_normalizer_iff_map_eq _ _).2 ((c.pair.rho_mem_baseSubgroup_iff q).1 hbase)
  have h2 := c.pair.rho_of_normalizes q hqn
  rw [hr] at h2
  obtain ⟨h3, h4⟩ := base_injective.1 h2
  refine ⟨fun k hk => (conjAutOf_eq_one_iff _ hqn |>.1 h3.symm) k hk, fun y => ?_⟩
  have h5 := congrArg (fun f : MulAut ↥c.L₁ => ((f y : ↥c.L₁) : G)) h4
  simp only [conjAutOf_apply] at h5
  have e1 : t⁻¹ * (q : G) * t = t * (q : G) * t := by rw [hti]
  rw [e1]
  exact h5.symm

theorem exists_pgl29_involution {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (c : InnerD8Config L t) (hρ : c.rho.range = ⊤)
    (hA6 : ∀ a : alternatingGroup (Fin 6), orderOf a = 5 →
      ∃ γ : MulAut (alternatingGroup (Fin 6)), γ * γ = 1 ∧ γ a = a ∧
        γ ∉ (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ∧
        ∀ b : alternatingGroup (Fin 6), orderOf b = 3 → γ b ≠ b)
    (f₀ : G) (hf₀ : f₀ ∈ c.L₁) (h5 : orderOf f₀ = 5)
    (hmod : ∀ a ∈ centralizer ({c.u} : Set G) ⊓
          centralizer ((zpowers f₀ ⊔ zpowers (t * f₀ * t⁻¹) : Subgroup G) : Set G),
        ∀ b ∈ centralizer ({c.u} : Set G) ⊓
          centralizer ((zpowers f₀ ⊔ zpowers (t * f₀ * t⁻¹) : Subgroup G) : Set G),
        a * b * a⁻¹ * b⁻¹ ∈ zpowers f₀ ⊔ zpowers (t * f₀ * t⁻¹) ∧
          a * a ∈ zpowers f₀ ⊔ zpowers (t * f₀ * t⁻¹)) :
    ∃ g : G, g * g = 1 ∧ g * c.u = c.u * g ∧ g * c.u₁ = c.u₁ * g ∧
      (∀ l ∈ c.L₁, g * l = l * g) ∧
      (∀ l ∈ c.L₁, g * (t * l * t⁻¹) * g⁻¹ ∈ conjSub t c.L₁) ∧
      (∀ a ∈ c.L₁, orderOf a = 3 → g * (t * a * t⁻¹) ≠ (t * a * t⁻¹) * g) ∧
      Nonempty (↥(conjSub t c.L₁ ⊔ zpowers g) ≃* ↥CFSG.QuasithinUnique.A6Models.pgl29) := by
  classical
  have ht2 : t * t = 1 := c.pair.t_sq
  have hti : t⁻¹ = t := c.pair.t_inv
  set e := c.eL₁ with he
  set f₁ : G := t * f₀ * t⁻¹ with hf₁
  set N₅ : Subgroup G := zpowers f₀ ⊔ zpowers f₁ with hN₅
  have ha5 : orderOf (e ⟨f₀, hf₀⟩) = 5 := by
    rw [MulEquiv.orderOf_eq]
    exact (Subgroup.orderOf_mk _ _).trans h5
  obtain ⟨γ, hγ2, hγfix, hγout, hγ3⟩ := hA6 _ ha5
  obtain ⟨q, hρq, hqL, hqt⟩ := c.exists_swap hρ γ
  have hqP : (q : G) ∈ c.P := q.2
  set s : G := t⁻¹ * (q : G) * t with hs
  have key : ∀ p k : G, Commute (t⁻¹ * p * t) k ↔ Commute p (t * k * t⁻¹) := by
    intro p k
    have := commute_conj_iff p k t⁻¹
    rwa [inv_inv] at this
  have hfixiff : ∀ y : ↥c.L₁, Commute s (y : G) ↔ γ (e y) = e y := by
    intro y
    constructor
    · intro h
      have h1 := hqt y
      have h2 : s * (y : G) * s⁻¹ = y := mul_inv_eq_iff_eq_mul.2 h.eq
      rw [h2] at h1
      have h3 : e.symm (γ (e y)) = y := Subtype.ext h1.symm
      exact (MulEquiv.symm_apply_eq e).1 h3
    · intro h
      have h1 := hqt y
      rw [h, MulEquiv.symm_apply_apply] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
  have hcomm01 : Commute f₀ f₁ := c.pair.comm f₀ hf₀ f₀ hf₀
  have hf₁A : f₁ ∈ conjSub t c.L₁ := ⟨f₀, hf₀, by simp [hf₁, MulAut.conj_apply]⟩
  have hqf₀ : Commute (q : G) f₀ := hqL f₀ hf₀
  have hqf₁ : Commute (q : G) f₁ := (key (q : G) f₀).1 ((hfixiff ⟨f₀, hf₀⟩).2 hγfix)
  have hcent : ∀ g : G, Commute g f₀ → Commute g f₁ → g ∈ centralizer (N₅ : Set G) := by
    intro g h0 h1
    have hle : N₅ ≤ centralizer ({g} : Set G) := by
      refine sup_le ((zpowers_le).2 ?_) ((zpowers_le).2 ?_)
      · rw [mem_centralizer_singleton_iff]; exact h0.symm.eq
      · rw [mem_centralizer_singleton_iff]; exact h1.symm.eq
    rw [mem_centralizer_iff]
    intro h hh
    have := hle hh
    rw [mem_centralizer_singleton_iff] at this
    exact this
  have hmodq := hmod (q : G) ⟨hqP, hcent _ hqf₀ hqf₁⟩ (q : G) ⟨hqP, hcent _ hqf₀ hqf₁⟩
  have hf₀5 : f₀ ^ 5 = 1 := h5 ▸ pow_orderOf_eq_one f₀
  have hf₁5 : f₁ ^ 5 = 1 := by
    have : orderOf f₁ = 5 := by
      rw [hf₁]
      have := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective f₀
      simpa [MulAut.conj_apply, h5] using this
    exact this ▸ pow_orderOf_eq_one f₁
  have hkey : ∀ x : ↥c.P, c.rho x = 1 → (x : G) ∈ N₅ → (x : G) = 1 := by
    intro x hx hxN
    have h4 : (x : G) ^ 4 = 1 := by
      have hk : x ∈ c.rho.ker := hx
      have h := pow_card_eq_one' (G := ↥c.rho.ker) (x := ⟨x, hk⟩)
      rw [c.card_ker_rho] at h
      have := congrArg (fun y : ↥c.rho.ker => ((y : ↥c.P) : G)) h
      simpa using this
    have h5' : (x : G) ^ 5 = 1 := pow_five_of_mem_sup hcomm01 hf₀5 hf₁5 hxN
    calc (x : G) = (x : G) ^ 5 * ((x : G) ^ 4)⁻¹ := by group
      _ = 1 := by rw [h4, h5']; simp
  have hqq : (q : G) * q = 1 := by
    have h1 : c.rho (q * q) = 1 := by
      rw [map_mul, hρq, base_mul_base, hγ2, mul_one, base_one]
    exact hkey (q * q) h1 hmodq.2
  have hu₁P : c.u₁ ∈ c.P := c.u₁_mem.1.1
  have hu₁L : ∀ k ∈ c.L₁, Commute c.u₁ k := fun k hk =>
    ((mem_centralizer_iff.1 c.u₁_mem.1.2) k hk).symm
  have hu₁Lt : ∀ k ∈ c.L₁, Commute c.u₁ (t * k * t⁻¹) := fun k hk =>
    ((mem_centralizer_iff.1 c.u₁_mem.2) (t * k * t⁻¹) ⟨k, hk, by simp [MulAut.conj_apply]⟩).symm
  have hu₁ρ : c.rho ⟨c.u₁, hu₁P⟩ = 1 := by
    have : (⟨c.u₁, hu₁P⟩ : ↥c.P) ∈ c.rho.ker := by
      rw [c.ker_rho, MonoidHom.mem_ker]
      exact (c.pair.rho_eq_one_iff _).2 ⟨hu₁L, hu₁Lt⟩
    exact this
  have hqu₁ : (q : G) * c.u₁ = c.u₁ * q := by
    have hmq := (hmod (q : G) ⟨hqP, hcent _ hqf₀ hqf₁⟩ c.u₁
      ⟨hu₁P, hcent _ (hu₁L f₀ hf₀) (hu₁Lt f₀ hf₀)⟩).1
    have h1 : c.rho (q * ⟨c.u₁, hu₁P⟩ * q⁻¹ * ⟨c.u₁, hu₁P⟩⁻¹) = 1 := by
      simp [hu₁ρ]
    have h2 := hkey _ h1 hmq
    have h3 : (q : G) * c.u₁ * (q : G)⁻¹ = c.u₁ := mul_inv_eq_one.1 h2
    exact mul_inv_eq_iff_eq_mul.1 h3
  have hAmem : ∀ a : G, a ∈ conjSub t c.L₁ ↔ ∃ l ∈ c.L₁, a = t * l * t⁻¹ := by
    intro a
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, by simp [MulAut.conj_apply]⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, by simp [MulAut.conj_apply]⟩
  have hconj : ∀ l : G, (q : G) * (t * l * t⁻¹) * (q : G)⁻¹ = t * (s * l * s⁻¹) * t⁻¹ := by
    intro l
    rw [hs]
    group
  have hslL : ∀ l : ↥c.L₁, s * (l : G) * s⁻¹ = ((e.symm (γ (e l)) : ↥c.L₁) : G) := hqt
  have hn : ∀ a ∈ conjSub t c.L₁, (q : G) * a * (q : G)⁻¹ ∈ conjSub t c.L₁ := by
    intro a ha
    obtain ⟨l, hl, rfl⟩ := (hAmem a).1 ha
    rw [hconj, hslL ⟨l, hl⟩]
    exact (hAmem _).2 ⟨_, (e.symm (γ (e ⟨l, hl⟩))).2, rfl⟩
  have hfix : ∀ a ∈ c.L₁, orderOf a = 3 →
      (q : G) * (t * a * t⁻¹) ≠ (t * a * t⁻¹) * q := by
    intro a ha ha3 hcm
    have h1 : Commute s a := (key (q : G) a).2 hcm
    have h2 := (hfixiff ⟨a, ha⟩).1 h1
    have h3 : orderOf (e ⟨a, ha⟩) = 3 := by
      rw [MulEquiv.orderOf_eq]
      exact (Subgroup.orderOf_mk _ _).trans ha3
    exact hγ3 _ h3 h2
  have hout : ∀ b ∈ conjSub t c.L₁, ∃ a ∈ conjSub t c.L₁,
      (q : G) * a * (q : G)⁻¹ ≠ b * a * b⁻¹ := by
    intro b hb
    by_contra hcon
    push Not at hcon
    obtain ⟨b₀, hb₀, rfl⟩ := (hAmem b).1 hb
    apply hγout
    refine ⟨e ⟨b₀, hb₀⟩, ?_⟩
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    have h1 := hcon (t * (y : G) * t⁻¹) ((hAmem _).2 ⟨y, y.2, rfl⟩)
    rw [hconj, hslL y] at h1
    have h2 : t * (b₀ * (y : G) * b₀⁻¹) * t⁻¹ = t * ((e.symm (γ (e y)) : ↥c.L₁) : G) * t⁻¹ := by
      rw [h1]; group
    have h3 : b₀ * (y : G) * b₀⁻¹ = ((e.symm (γ (e y)) : ↥c.L₁) : G) :=
      mul_left_cancel (mul_right_cancel h2)
    have h4 : (⟨b₀, hb₀⟩ * y * ⟨b₀, hb₀⟩⁻¹ : ↥c.L₁) = e.symm (γ (e y)) := Subtype.ext h3
    have h5' : γ (e y) = e (⟨b₀, hb₀⟩ * y * ⟨b₀, hb₀⟩⁻¹) := by
      rw [h4, MulEquiv.apply_symm_apply]
    rw [MulAut.conj_apply, h5', map_mul, map_mul, map_inv]
  have hnot : (q : G) ∉ conjSub t c.L₁ := by
    intro hq
    obtain ⟨a, _, ha⟩ := hout _ hq
    exact ha rfl
  have hβfix : ∀ a ∈ conjSub t c.L₁, orderOf a = 3 → (q : G) * a * (q : G)⁻¹ ≠ a := by
    intro a ha ha3 hcm
    obtain ⟨l, hl, rfl⟩ := (hAmem a).1 ha
    have hl3 : orderOf l = 3 := by
      have := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective l
      rw [← ha3, ← this]
      simp [MulAut.conj_apply]
    exact hfix l hl hl3 (mul_inv_eq_iff_eq_mul.1 hcm)
  refine ⟨q, hqq, ((mem_centralizer_iff.1 hqP c.u (Set.mem_singleton _)).symm), hqu₁,
    fun l hl => (hqL l hl).eq, fun l hl => hn _ ((hAmem _).2 ⟨l, hl, rfl⟩), hfix, ?_⟩
  let e' : ↥(conjSub t c.L₁) ≃* alternatingGroup (Fin 6) :=
    (Subgroup.equivMapOfInjective c.L₁ (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).symm.trans e
  exact nonempty_mulEquiv_pgl29_of_type (conjSub t c.L₁ ⊔ zpowers (q : G)) (q : G)
    (conjSub t c.L₁) le_sup_left e' (mem_sup_right (mem_zpowers _)) hqq hnot rfl hn hβfix hout

end InnerD8Config

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
