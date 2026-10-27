module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Base

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup

theorem isComponentOf_conj {M : Type*} [Group M] {P B : Subgroup M} {g t : M} (hg : g ∈ P)
    (hB : Assembly.IsComponentOf B (P ⊓ centralizer ({g * t * g⁻¹} : Set M))) :
    Assembly.IsComponentOf (B.map (MulAut.conj g⁻¹).toMonoidHom)
      (P ⊓ centralizer ({t} : Set M)) := by
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have h := (LocalAnalysis.ComponentInitial.isComponentOf_map_iff hinj).2 hB
  have hmap : (P ⊓ centralizer ({g * t * g⁻¹} : Set M)).map (MulAut.conj g⁻¹).toMonoidHom =
      P ⊓ centralizer ({t} : Set M) := by
    ext y
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨x, ⟨hxP, hx⟩, rfl⟩
      refine ⟨P.mul_mem (P.mul_mem (P.inv_mem hg) hxP) hg, ?_⟩
      calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
        _ = t * (g⁻¹ * x * g) := by group
    · rintro ⟨hyP, hy⟩
      refine ⟨g * y * g⁻¹, ⟨P.mul_mem (P.mul_mem hg hyP) (P.inv_mem hg), ?_⟩, by group⟩
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [hy]
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
  rwa [hmap] at h

theorem le_of_isSubnormal {M : Type*} [Group M] {H K : Subgroup M}
    (h : Assembly.IsSubnormal H K) : H ≤ K :=
  h.le

theorem mem_of_isSubnormal_of_odd {M : Type*} [Group M] [Finite M] {H K : Subgroup M}
    (h : Assembly.IsSubnormal H K) {x : M} (hodd : Odd (orderOf x)) (hx : x ∈ K) :
    ∀ k : ℕ, Nat.card K = 2 ^ k * Nat.card H → x ∈ H := by
  induction h with
  | refl => exact fun _ _ => hx
  | @step H L K hle hn hLK ih =>
    intro k hk
    have hLK' := le_of_isSubnormal hLK
    have h1 : Nat.card L = Nat.card H * (H.subgroupOf L).index := by
      rw [← Subgroup.card_mul_index (H.subgroupOf L),
        Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    have h2 : Nat.card K = Nat.card L * (L.subgroupOf K).index := by
      rw [← Subgroup.card_mul_index (L.subgroupOf K),
        Nat.card_congr (subgroupOfEquivOfLe hLK').toEquiv]
    have hH0 : 0 < Nat.card H := Nat.card_pos
    have hij : (H.subgroupOf L).index * (L.subgroupOf K).index = 2 ^ k := by
      have : Nat.card H * ((H.subgroupOf L).index * (L.subgroupOf K).index) =
          Nat.card H * 2 ^ k := by
        rw [← mul_assoc, ← h1, ← h2, hk, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hH0 this
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hij)
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hij)
    have hxL : x ∈ L := ih hx b (by rw [h2, hb, mul_comm])
    have hq : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ H.subgroupOf L) = 1 := by
      have hd1 : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ H.subgroupOf L) ∣ orderOf x := by
        rw [← Subgroup.orderOf_mk x hxL]
        exact orderOf_map_dvd (QuotientGroup.mk' (H.subgroupOf L)) ⟨x, hxL⟩
      have hd2 := orderOf_dvd_natCard (QuotientGroup.mk (⟨x, hxL⟩ : L) : L ⧸ H.subgroupOf L)
      rw [← Subgroup.index_eq_card, ha] at hd2
      obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
      rcases c with _ | c
      · simpa using hc
      · exfalso
        have : 2 ∣ orderOf x := (dvd_pow_self 2 (Nat.succ_ne_zero c)).trans (hc ▸ hd1)
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    have := (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 hq)
    exact mem_subgroupOf.mp this

theorem card_inf_centralizer {M : Type*} [Group M] (P : Subgroup M) (x : P) :
    Nat.card (centralizer ({x} : Set P)) = Nat.card ↥(P ⊓ centralizer ({(x : M)} : Set M)) := by
  have hmap : (centralizer ({x} : Set P)).map P.subtype = P ⊓ centralizer ({(x : M)} : Set M) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine mem_inf.mpr ⟨z.2, ?_⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hz
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hz
    · intro hy
      obtain ⟨hyP, hy⟩ := mem_inf.mp hy
      refine ⟨⟨y, hyP⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rw [mem_centralizer_singleton_iff] at hy
      exact Subtype.ext hy
  rw [← hmap, card_map_of_injective P.subtype_injective]

theorem coset_of_mulAut_outer {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hC : centralizer (N : Set G) = ⊥) {Y : Type*} [Group Y] (e : N ≃* Y) (β : MulAut Y)
    (h : ∀ φ : MulAut Y, orderOf φ = 2 → φ ∉ OuterAutomorphisms.inner Y →
      ∃ g : Y, φ = MulAut.conj g * β * (MulAut.conj g)⁻¹)
    {α : G} (hα : orderOf α = 2) (hαN : α ∉ N) :
    ∀ x : G, orderOf x = 2 → α⁻¹ * x ∈ N → ∃ γ ∈ N, γ⁻¹ * α * γ = x := by
  intro x hx hαx
  let ρ : G →* MulAut Y := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : MulAut.conjNormal y = 1 := (MulAut.congr e).injective (by rw [map_one]; exact hy)
    have h2 : y ∈ centralizer (N : Set G) := by
      rw [mem_centralizer_iff]
      intro n hn
      have := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : G)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc n * y = y * n * y⁻¹ * y := by rw [this]
        _ = y * n := by group
    rw [hC] at h2
    exact h2
  have hρN : ∀ n : N, ρ n = MulAut.conj (e n) := by
    intro n
    have hcn : MulAut.conjNormal (n : G) = MulAut.conj n :=
      MulEquiv.ext fun m => Subtype.ext (by simp [MulAut.conjNormal_apply])
    rw [← OuterAutomorphisms.congr_conj e n, ← hcn]
    rfl
  have hout : ∀ y : G, y ∉ N → orderOf y = 2 → orderOf (ρ y) = 2 ∧
      ρ y ∉ OuterAutomorphisms.inner Y := by
    intro y hy hy2
    refine ⟨by rw [orderOf_injective ρ hρinj, hy2], fun hin => hy ?_⟩
    refine mem_of_conjNormal_mem_inner hC (mem_inner_of_congr e ?_)
    exact hin
  have hxN : x ∉ N := fun hxN => hαN (by
    have := N.mul_mem hxN (N.inv_mem hαx)
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this)
  obtain ⟨hα2, hαo⟩ := hout α hαN hα
  obtain ⟨hx2, hxo⟩ := hout x hxN hx
  obtain ⟨g₁, hg₁⟩ := h _ hα2 hαo
  obtain ⟨g₂, hg₂⟩ := h _ hx2 hxo
  set c : N := e.symm (g₂ * g₁⁻¹) with hc
  have hρc : ρ c = MulAut.conj g₂ * (MulAut.conj g₁)⁻¹ := by
    rw [hρN, hc, MulEquiv.apply_symm_apply, map_mul, map_inv]
  refine ⟨((c : G))⁻¹, N.inv_mem c.2, ?_⟩
  rw [inv_inv]
  apply hρinj
  rw [map_mul, map_mul, map_inv, hρc, hg₂, hg₁]
  group

theorem false_of_small_dvd_192 {X : Type} [Group X]
    (h : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel X .PSL 2 p f) ∨
      Nonempty (X ≃* alternatingGroup (Fin 7))) (hd : Nat.card X ∣ 192) : False := by
  rcases card_small h with ⟨q, hq, hq5, hX⟩ | hX
  · rw [hX] at hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have hq9 : q < 9 := by
      by_contra hq9
      push Not at hq9
      have : 9 * (9 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul hq9 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq9 2) 1)
      omega
    interval_cases q <;> simp_all
  · rw [hX] at hd
    omega

theorem card_eq_sixty_of_dvd {X : Type} [Group X]
    (h : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel X .PSL 2 p f) ∨
      Nonempty (X ≃* alternatingGroup (Fin 7))) (hd : Nat.card X ∣ 240) : Nat.card X = 60 := by
  rcases card_small h with ⟨q, hq, hq5, hX⟩ | hX
  · rw [hX] at hd ⊢
    have hle := Nat.le_of_dvd (by norm_num) hd
    have hq9 : q < 9 := by
      by_contra hq9
      push Not at hq9
      have : 9 * (9 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul hq9 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq9 2) 1)
      omega
    interval_cases q <;> simp_all
  · rw [hX] at hd
    omega

end CFSG.ComponentClassification.GSThmB.CF23I
