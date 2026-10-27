module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Comps
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Gen
public import CFSG.GH74.GLS.Stage2.Final.ModelIVK410

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5

namespace CFSG.GH74.Ivk413

variable {F : Type} [Field F] {M : ModelData F} {H : Type} [Group H] (K : Subgroup H)

theorem map_centralizer_Phi {z : H} (hz : z ∈ K) (Φ : ↥K ≃* PG M) (hΦ : Φ ⟨z, hz⟩ = yP M) :
    (centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)).map Φ.toMonoidHom = Cg M := by
  rw [ModelLT.centralizer_map_equiv Φ ⟨z, hz⟩, hΦ]

theorem Ez_map_Phi [Finite F] {z : H} (hz : z ∈ K) (Φ : ↥K ≃* PG M) (hΦ : Φ ⟨z, hz⟩ = yP M)
    (hG : GoodModel M) :
    (IVK.Ez (⟨z, hz⟩ : ↥K)).map Φ.toMonoidHom = K1 M ⊔ K2 M := by
  rw [Ez_map_equiv Φ ⟨z, hz⟩, hΦ]
  exact layer_map_eq M hG.two_ne_zero hG.qs

theorem clause2 [Finite F] (hG : GoodModel M) {z : H} (hz : z ∈ K) (Φ : ↥K ≃* PG M)
    (hΦ : Φ ⟨z, hz⟩ = yP M)
    (hratio : (Nat.card ↥(Cg M) / Nat.card ↥(K1 M ⊔ K2 M)).factorization 2 = 2) :
    (Nat.card ↥(centralizer ({z} : Set H) ⊓ K) /
      Nat.card ↥((layer ↥(centralizer ({z} : Set H) ⊓ K)).map
        (centralizer ({z} : Set H) ⊓ K).subtype)).factorization 2 = 2 := by
  rw [card_centralizer_inf K hz, card_layer_centralizer_inf K hz]
  have h1 : Nat.card ↥(centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)) = Nat.card ↥(Cg M) := by
    rw [← map_centralizer_Phi K hz Φ hΦ, Subgroup.card_map_of_injective Φ.injective]
  have h2 : Nat.card ↥(IVK.Ez (⟨z, hz⟩ : ↥K)) = Nat.card ↥(K1 M ⊔ K2 M) := by
    rw [← Ez_map_Phi K hz Φ hΦ hG, Subgroup.card_map_of_injective Φ.injective]
  rw [h1, h2]
  exact hratio

theorem pPrimeCoreOf_inf_eq_map {z : H} (hz : z ∈ K) :
    pPrimeCoreOf 2 (centralizer ({z} : Set H) ⊓ K) =
      (pPrimeCoreOf 2 (centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K))).map K.subtype := by
  rw [centralizer_inf_eq_map K hz, pPrimeCoreOf_map_injective K.subtype K.subtype_injective]

theorem pPrimeCoreOf_map_Phi {z : H} (hz : z ∈ K) (Φ : ↥K ≃* PG M) (hΦ : Φ ⟨z, hz⟩ = yP M) :
    (pPrimeCoreOf 2 (centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K))).map Φ.toMonoidHom =
      pPrimeCoreOf 2 (Cg M) := by
  rw [← map_centralizer_Phi K hz Φ hΦ, pPrimeCoreOf_map_injective Φ.toMonoidHom Φ.injective]

theorem isCompIn_Phi {z : H} (hz : z ∈ K) (Φ : ↥K ≃* PG M) (hΦ : Φ ⟨z, hz⟩ = yP M)
    {K₁ : Subgroup H} (hK₁ : K₁ ≤ centralizer ({z} : Set H) ⊓ K)
    (hcomp : IsComponent (K₁.subgroupOf (centralizer ({z} : Set H) ⊓ K))) :
    IsCompIn (Cg M) ((K₁.subgroupOf K).map Φ.toMonoidHom) := by
  have hle : K₁.subgroupOf K ≤ centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K) := by
    intro x hx
    have h1 : (x : H) ∈ centralizer ({z} : Set H) := (Subgroup.mem_inf.1 (hK₁ hx)).1
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext h1
  have hmap : (K₁.subgroupOf (centralizer ({z} : Set H) ⊓ K)).map (eqCK K hz).symm.toMonoidHom =
      (K₁.subgroupOf K).subgroupOf (centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)) := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulEquiv.symm_symm, mem_subgroupOf]
    rfl
  have hc : IsComponent ((K₁.subgroupOf K).subgroupOf (centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K))) := by
    rw [← hmap]
    exact CFSG.LocalCores.isComponent_map_mulEquiv _ hcomp
  have := ModelLUT.isCompIn_map Φ (X := centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K))
    (K := K₁.subgroupOf K) ⟨hle, hc⟩
  rwa [map_centralizer_Phi K hz Φ hΦ] at this

theorem clause4 [Finite F] (hG : GoodModel M) {z : H} (hz : z ∈ K) (Φ : ↥K ≃* PG M)
    (hΦ : Φ ⟨z, hz⟩ = yP M) {K₁ : Subgroup H} (hK₁ : K₁ ≤ centralizer ({z} : Set H) ⊓ K)
    (hcomp : IsComponent (K₁.subgroupOf (centralizer ({z} : Set H) ⊓ K)))
    {y : H} (hy : y ∈ pPrimeCoreOf 2 (centralizer ({z} : Set H) ⊓ K))
    {g : H} (hg : g ∈ K ⊓ normalizer (K₁ : Set H)) : g * y = y * g := by
  obtain ⟨hgK, hgN⟩ := hg
  have hL := isCompIn_Phi K hz Φ hΦ hK₁ hcomp
  have hnorm : Φ ⟨g, hgK⟩ ∈ normalizer (((K₁.subgroupOf K).map Φ.toMonoidHom : Subgroup (PG M)) :
      Set (PG M)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, mem_subgroupOf, mem_subgroupOf]
    have e : Φ.symm (Φ ⟨g, hgK⟩ * w * (Φ ⟨g, hgK⟩)⁻¹) = ⟨g, hgK⟩ * Φ.symm w * ⟨g, hgK⟩⁻¹ := by
      simp
    rw [e]
    simpa using Subgroup.mem_normalizer_iff.1 hgN ((Φ.symm w : ↥K) : H)
  have hgC0 : Φ ⟨g, hgK⟩ ∈ C0 M := by
    rcases only_comps' hG hL with h | h
    · exact normalizer_K1_le_C0 hG (by rw [← h]; exact hnorm)
    · exact normalizer_K2_le_C0 hG (by rw [← h]; exact hnorm)
  rw [pPrimeCoreOf_inf_eq_map K hz] at hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
  have hyBS : Φ y' ∈ BSsub M :=
    pPrimeCoreOf_le_BS hG (by rw [← pPrimeCoreOf_map_Phi K hz Φ hΦ]; exact Subgroup.mem_map_of_mem _ hy')
  have h1 := bs_comm_C0 hG hyBS hgC0
  have h2 : y' * ⟨g, hgK⟩ = ⟨g, hgK⟩ * y' := Φ.injective (by simpa using h1)
  exact (congrArg Subtype.val h2).symm


section Clause3

variable {F : Type} [Field F] {M : ModelData F}

theorem aut_odd_normalizes [Finite F] (hG : GoodModel M) (β : MulAut (PG M))
    (hβy : β (yP M) = yP M) (hodd : Odd (orderOf β)) :
    (K1 M).map β.toMonoidHom = K1 M ∧ (K2 M).map β.toMonoidHom = K2 M := by
  have hC : (Cg M).map β.toMonoidHom = Cg M := by
    rw [ModelLT.centralizer_map_equiv β (yP M), hβy]
  have h1 : IsCompIn (Cg M) ((K1 M).map β.toMonoidHom) := by
    have := ModelLUT.isCompIn_map β (isCompIn_K1 hG)
    rwa [hC] at this
  have h2 : IsCompIn (Cg M) ((K2 M).map β.toMonoidHom) := by
    have := ModelLUT.isCompIn_map β (isCompIn_K2 hG)
    rwa [hC] at this
  have hne : (K1 M).map β.toMonoidHom ≠ (K2 M).map β.toMonoidHom := fun h =>
    K1_ne_K2 hG (Subgroup.map_injective β.injective h)
  rcases only_comps' hG h1 with e1 | e1 <;> rcases only_comps' hG h2 with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · exact ⟨e1, e2⟩
  ·
    exfalso
    have key : ∀ k : ℕ, ((K1 M).map (β ^ k).toMonoidHom = if k % 2 = 0 then K1 M else K2 M) ∧
        ((K2 M).map (β ^ k).toMonoidHom = if k % 2 = 0 then K2 M else K1 M) := by
      intro k
      induction k with
      | zero =>
        have : ((1 : MulAut (PG M)) : PG M →* PG M) = MonoidHom.id _ := by ext; rfl
        simp [this]
      | succ k ih =>
        have hmap : ∀ L : Subgroup (PG M),
            L.map (β ^ (k + 1)).toMonoidHom = (L.map β.toMonoidHom).map (β ^ k).toMonoidHom := by
          intro L
          rw [Subgroup.map_map]
          congr 1
        rw [hmap, hmap, e1, e2]
        obtain ⟨ih1, ih2⟩ := ih
        rw [ih1, ih2]
        by_cases hk : k % 2 = 0
        · have hk' : (k + 1) % 2 ≠ 0 := by omega
          simp [hk, hk']
        · have hk' : (k + 1) % 2 = 0 := by omega
          simp [hk, hk']
    obtain ⟨n, hn⟩ := hodd
    have h1' := (key (orderOf β)).1
    rw [pow_orderOf_eq_one] at h1'
    have h1id : MulEquiv.toMonoidHom (1 : MulAut (PG M)) = MonoidHom.id (PG M) := by ext; rfl
    rw [h1id, Subgroup.map_id, hn] at h1'
    simp at h1'
    exact K1_ne_K2 hG h1'
  · exact absurd (e1.trans e2.symm) hne

@[expose] def AutInner (M : ModelData F) : Prop :=
  ∀ β : MulAut (PG M), Odd (orderOf β) → (∀ g ∈ K1 M, β g = g) →
    ∃ k : PG M, β = MulAut.conj k

variable {H : Type} [Group H]

theorem oddCore_le_K [Finite F] [Finite H] (hG : GoodModel M) (hAut : AutInner M)
    (K : Subgroup H) [K.Normal] (hC : centralizer (K : Set H) = ⊥)
    {z : H} (hz : z ∈ K) (Φ : ↥K ≃* PG M) (hΦ : Φ ⟨z, hz⟩ = yP M)
    {y : H} (hy : y ∈ pPrimeCoreOf 2 (centralizer ({z} : Set H))) : y ∈ K := by
  have hyC : y ∈ centralizer ({z} : Set H) := pPrimeCoreOf_le _ hy
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
  have hyodd : Odd (orderOf y) :=
    Odd.of_dvd_nat (odd_card_pPrimeCoreOf _) (Subgroup.orderOf_dvd_natCard _ hy)
  let α : MulAut ↥K := MulAut.conjNormal y
  let β : MulAut (PG M) := MulAut.congr Φ α
  have hβ : ∀ g : PG M, β g = Φ (α (Φ.symm g)) := fun g => by
    simp [β, MulAut.congr_apply]
  have hαx : ∀ x : ↥K, ((α x : ↥K) : H) = y * (x : H) * y⁻¹ := fun x => MulAut.conjNormal_apply y x
  have hαz : α ⟨z, hz⟩ = ⟨z, hz⟩ := by
    apply Subtype.ext
    rw [hαx]
    show y * z * y⁻¹ = z
    rw [hyz]
    group
  have hβy : β (yP M) = yP M := by
    rw [hβ, ← hΦ, MulEquiv.symm_apply_apply, hαz]
  have hβodd : Odd (orderOf β) := by
    refine Odd.of_dvd_nat hyodd (orderOf_dvd_of_pow_eq_one ?_)
    have h1 : α ^ orderOf y = 1 := by
      have : α ^ orderOf y = MulAut.conjNormal (y ^ orderOf y) := by rw [map_pow]
      rw [this, pow_orderOf_eq_one, map_one]
    show (MulAut.congr Φ α) ^ orderOf y = 1
    rw [← map_pow, h1, map_one]
  obtain ⟨hK1, hK2⟩ := aut_odd_normalizes hG β hβy hβodd
  have hKβ : ∀ g ∈ K1 M, β g ∈ K1 M := fun g hg => by
    have : β g ∈ (K1 M).map β.toMonoidHom := ⟨g, hg, rfl⟩
    rwa [hK1] at this
  have hCg_C : ∀ g ∈ K1 M, ((Φ.symm g : ↥K) : H) ∈ centralizer ({z} : Set H) := by
    intro g hg
    have h := Subgroup.mem_centralizer_singleton_iff.1 (K1_le_Cg M hg)
    rw [mem_centralizer_singleton_iff]
    have h' : Φ.symm g * ⟨z, hz⟩ = ⟨z, hz⟩ * Φ.symm g := by
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hΦ]
      exact h
    exact congrArg Subtype.val h'
  have hfix : ∀ g ∈ K1 M, β g = g := by
    intro g hg
    set κ : ↥K := Φ.symm g with hκ
    have hgκ : Φ κ = g := Φ.apply_symm_apply g
    have hκC : (κ : H) ∈ centralizer ({z} : Set H) := hCg_C g hg
    let c : ↥K := α κ * κ⁻¹
    have hcY : (c : H) ∈ pPrimeCoreOf 2 (centralizer ({z} : Set H)) := by
      have e : (c : H) = y * ((κ : H) * y⁻¹ * (κ : H)⁻¹) := by
        simp only [c, Subgroup.coe_mul, Subgroup.coe_inv, hαx]; group
      rw [e]
      exact (pPrimeCoreOf 2 _).mul_mem hy (pPrimeCoreOf_conj hκC ((pPrimeCoreOf 2 _).inv_mem hy))
    have hΦα : Φ (α κ) = β g := (hβ g).symm
    have hcK1 : Φ c ∈ K1 M := by
      rw [map_mul, map_inv, hgκ, hΦα]
      exact (K1 M).mul_mem (hKβ g hg) ((K1 M).inv_mem hg)
    let N₁ : Subgroup (PG M) :=
      K1 M ⊓ ((pPrimeCoreOf 2 (centralizer ({z} : Set H))).subgroupOf K).map Φ.toMonoidHom
    have hN₁ : Φ c ∈ N₁ := ⟨hcK1, c, hcY, rfl⟩
    have hodd : Odd (Nat.card N₁) := by
      have h1 : Nat.card N₁ ∣ Nat.card (((pPrimeCoreOf 2 (centralizer ({z} : Set H))).subgroupOf K).map
          Φ.toMonoidHom) := Subgroup.card_dvd_of_le inf_le_right
      rw [Subgroup.card_map_of_injective Φ.injective] at h1
      have h2 : Nat.card ((pPrimeCoreOf 2 (centralizer ({z} : Set H))).subgroupOf K) ∣
          Nat.card (pPrimeCoreOf 2 (centralizer ({z} : Set H))) := by
        rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact Odd.of_dvd_nat (odd_card_pPrimeCoreOf _) (dvd_trans h1 h2)
    have hbot : N₁ = ⊥ := by
      refine odd_normal_K1 hG N₁ inf_le_left ?_ hodd
      rintro k hk n ⟨hnK, ν, hν, rfl⟩
      have hkC := hCg_C k hk
      refine ⟨(K1 M).mul_mem ((K1 M).mul_mem hk hnK) ((K1 M).inv_mem hk), Φ.symm k * ν * (Φ.symm k)⁻¹, ?_, ?_⟩
      · have hν' : (ν : H) ∈ pPrimeCoreOf 2 (centralizer ({z} : Set H)) := hν
        show ((Φ.symm k * ν * (Φ.symm k)⁻¹ : ↥K) : H) ∈ pPrimeCoreOf 2 (centralizer ({z} : Set H))
        simpa using pPrimeCoreOf_conj hkC hν'
      · simp
    rw [hbot, Subgroup.mem_bot] at hN₁
    have hc1 : c = 1 := Φ.injective (by rw [hN₁, map_one])
    have : α κ = κ := by
      have := congrArg (· * κ) hc1
      simpa [c] using this
    rw [← hΦα, this, hgκ]
  obtain ⟨k₀, hk₀⟩ := hAut β hβodd hfix
  set x₀ : ↥K := Φ.symm k₀ with hx₀
  have hα : ∀ x : ↥K, α x = x₀ * x * x₀⁻¹ := by
    intro x
    apply Φ.injective
    have h1 := hβ (Φ x)
    rw [MulEquiv.symm_apply_apply] at h1
    rw [← h1, hk₀]
    simp [hx₀]
  have hcomm : ∀ h ∈ K, h * ((x₀ : H)⁻¹ * y) = ((x₀ : H)⁻¹ * y) * h := by
    intro h hh
    have e : (x₀ : H) * h * (x₀ : H)⁻¹ = y * h * y⁻¹ := by
      have := congrArg Subtype.val (hα ⟨h, hh⟩)
      rw [hαx] at this
      simpa using this.symm
    calc h * ((x₀ : H)⁻¹ * y) = (x₀ : H)⁻¹ * ((x₀ : H) * h * (x₀ : H)⁻¹) * y := by group
      _ = (x₀ : H)⁻¹ * (y * h * y⁻¹) * y := by rw [e]
      _ = ((x₀ : H)⁻¹ * y) * h := by group
  have hu : (x₀ : H)⁻¹ * y ∈ centralizer (K : Set H) := Subgroup.mem_centralizer_iff.2 hcomm
  rw [hC, Subgroup.mem_bot] at hu
  have : y = (x₀ : H) := by
    have := congrArg ((x₀ : H) * ·) hu
    simpa using this
  rw [this]
  exact x₀.2

theorem clause3 [Finite F] [Finite H] (hG : GoodModel M) (hAut : AutInner M)
    (K : Subgroup H) [K.Normal] (hC : centralizer (K : Set H) = ⊥)
    {z : H} (hz : z ∈ K) (Φ : ↥K ≃* PG M) (hΦ : Φ ⟨z, hz⟩ = yP M) :
    pPrimeCoreOf 2 (centralizer ({z} : Set H) ⊓ K) = pPrimeCoreOf 2 (centralizer ({z} : Set H)) := by
  apply le_antisymm
  · refine le_pPrimeCoreOf_of_normal_odd ?_ ?_ (odd_card_pPrimeCoreOf _)
    · exact (pPrimeCoreOf_le _).trans inf_le_left
    · intro x hx n hn
      refine conj_mem_pPrimeCoreOf ?_ ?_ hn
      · intro w hw
        obtain ⟨hwC, hwK⟩ := Subgroup.mem_inf.1 hw
        exact Subgroup.mem_inf.2 ⟨(centralizer ({z} : Set H)).mul_mem
          ((centralizer ({z} : Set H)).mul_mem hx hwC) ((centralizer ({z} : Set H)).inv_mem hx),
          Subgroup.Normal.conj_mem inferInstance w hwK x⟩
      · intro w hw
        obtain ⟨hwC, hwK⟩ := Subgroup.mem_inf.1 hw
        refine Subgroup.mem_inf.2 ⟨(centralizer ({z} : Set H)).mul_mem
          ((centralizer ({z} : Set H)).mul_mem ((centralizer ({z} : Set H)).inv_mem hx) hwC) hx, ?_⟩
        simpa using Subgroup.Normal.conj_mem inferInstance w hwK x⁻¹
  · have hK : pPrimeCoreOf 2 (centralizer ({z} : Set H)) ≤ K := fun y hy =>
      oddCore_le_K hG hAut K hC hz Φ hΦ hy
    refine le_pPrimeCoreOf_of_normal_odd (le_inf (pPrimeCoreOf_le _) hK) ?_ (odd_card_pPrimeCoreOf _)
    intro x hx n hn
    exact pPrimeCoreOf_conj (Subgroup.mem_inf.1 hx).1 hn



end Clause3

end CFSG.GH74.Ivk413
