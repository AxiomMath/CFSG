module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FusionModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux

public section

namespace CFSG.QuasithinUnique.A6Fusion

open Equiv A6Models CFSG.Open

theorem isFourSubgroup_map {G G' : Type} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {E : Subgroup G} (hE : IsFourSubgroup E) :
    IsFourSubgroup (E.map f) := by
  obtain ⟨⟨hc, hx⟩, hcard⟩ := hE
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have := hc
    infer_instance
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hx a ha, map_one]
  · rw [Subgroup.card_map_of_injective hf, hcard]

theorem isFourSubgroup_subgroupOf {G : Type} [Group G] {K E : Subgroup G} (hEK : E ≤ K)
    (hE : IsFourSubgroup E) : IsFourSubgroup (E.subgroupOf K) := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have ha : ((a : K) : G) ∈ E := a.2
    have hb : ((b : K) : G) ∈ E := b.2
    exact Subtype.ext (Subtype.ext (isElemAbelian_mul_comm hE.1 ha hb))
  · have hx' : (x : G) ∈ E := hx
    have h2 : (x : G) ^ 2 = 1 := hE.1.2 _ hx'
    exact Subtype.ext h2
  · rw [← hE.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv

theorem isSylowTwoOf_map_range {G W : Type*} [Group G] [Group W] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* W) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS.le).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

theorem card_le_eight_of_dvd {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    (hX : IsPGroup 2 X) (hdvd : Nat.card X ∣ 360) : Nat.card X ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hX.exists_card_eq
  rw [hj] at hdvd ⊢
  by_contra hcon
  have hj4 : 4 ≤ j := by
    by_contra h4
    have : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h16 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 hj4
  have := h16.trans hdvd
  norm_num at this

theorem conj_conj_inv {W : Type*} [Group W] (E : Subgroup W) (b : W) :
    (E.map (MulAut.conj b).toMonoidHom).map (MulAut.conj b⁻¹).toMonoidHom = E := by
  rw [Subgroup.map_map]
  have : (MulAut.conj b⁻¹).toMonoidHom.comp (MulAut.conj b).toMonoidHom = MonoidHom.id W := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [this, Subgroup.map_id]

theorem conj_inv_conj {W : Type*} [Group W] (E : Subgroup W) (b : W) :
    (E.map (MulAut.conj b⁻¹).toMonoidHom).map (MulAut.conj b).toMonoidHom = E := by
  simpa using conj_conj_inv E b⁻¹

theorem conj_conj {W : Type*} [Group W] (E : Subgroup W) (a b : W) :
    (E.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      E.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem mem_conjugate_iff' {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem exists_swap {R F E₁ E₂ : Subgroup (Perm (Fin 10))}
    (hPnorm : ∀ a ∈ autA6, ∀ x ∈ psl29, a * x * a⁻¹ ∈ psl29)
    (hP : Nat.card psl29 = 360) (hR : IsSylowTwoOf R autA6)
    (hF : F ≤ R ⊓ psl29) (hF8 : Nat.card F = 8)
    (h₁ : E₁ ≤ F) (h₁4 : IsFourSubgroup E₁) (h₂ : E₂ ≤ F) (h₂4 : IsFourSubgroup E₂)
    (hne : E₁ ≠ E₂) :
    ∃ p ∈ R, E₂ = E₁.map (MulAut.conj p).toMonoidHom := by
  obtain ⟨R₀, hQR₀, hR₀⟩ := exists_isSylowTwoOf_of_le Q_le_autA6 isPGroup_Q
  obtain ⟨b, hb, hRb⟩ := hR₀.exists_conj hR
  have hD'R : D.map (MulAut.conj b).toMonoidHom ≤ R := by
    rw [hRb]
    exact Subgroup.map_mono (D_le_Q.trans hQR₀)
  have hD'P : D.map (MulAut.conj b).toMonoidHom ≤ psl29 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPnorm b hb x (D_le_psl29 hx)
  have hD'8 : Nat.card (D.map (MulAut.conj b).toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj b).injective]
    exact card_D
  have hRP2 : IsPGroup 2 ↥(R ⊓ psl29) := hR.isPGroup.to_le inf_le_left
  have hRP8 : Nat.card ↥(R ⊓ psl29) ≤ 8 :=
    card_le_eight_of_dvd hRP2 (hP ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hFeq : F = R ⊓ psl29 := Subgroup.eq_of_le_of_card_ge hF (by omega)
  have hD'eq : D.map (MulAut.conj b).toMonoidHom = R ⊓ psl29 :=
    Subgroup.eq_of_le_of_card_ge (le_inf hD'R hD'P) (by omega)
  have hFD : F = D.map (MulAut.conj b).toMonoidHom := hFeq.trans hD'eq.symm
  have hpull : ∀ {E : Subgroup (Perm (Fin 10))}, E ≤ F →
      E.map (MulAut.conj b⁻¹).toMonoidHom ≤ D := by
    intro E hE
    have := Subgroup.map_mono (f := (MulAut.conj b⁻¹).toMonoidHom) (hE.trans hFD.le)
    rwa [conj_conj_inv] at this
  have hinj : Function.Injective (MulAut.conj b⁻¹).toMonoidHom := (MulAut.conj b⁻¹).injective
  have hne' : E₁.map (MulAut.conj b⁻¹).toMonoidHom ≠ E₂.map (MulAut.conj b⁻¹).toMonoidHom := by
    intro h
    apply hne
    have := congrArg (fun X => X.map (MulAut.conj b).toMonoidHom) h
    simpa only [conj_inv_conj] using this
  have key := swap_four (hpull h₁) (hpull h₂) (isFourSubgroup_map hinj h₁4)
    (isFourSubgroup_map hinj h₂4) hne'
  refine ⟨b * pg * b⁻¹, ?_, ?_⟩
  · rw [hRb]
    exact ⟨pg, hQR₀ pg_mem_Q, by simp [MulAut.conj_apply]⟩
  · have h1 : (E₂.map (MulAut.conj b⁻¹).toMonoidHom).map (MulAut.conj b).toMonoidHom =
        ((E₁.map (MulAut.conj b⁻¹).toMonoidHom).map (MulAut.conj pg).toMonoidHom).map
          (MulAut.conj b).toMonoidHom := by rw [key]
    rw [conj_inv_conj, conj_conj, conj_conj] at h1
    exact h1

variable {G : Type} [Group G] [Finite G]

theorem fusion_of_hom {H K S : Subgroup G}
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hS : IsSylowTwoOf S H)
    (ρ : ↥H →* Perm (Fin 10)) (hρ : ρ.range = autA6)
    (ι : ↥K →* Perm (Fin 10)) (hι : Function.Injective ι) (hιr : ι.range = psl29)
    (hιρ : ∀ k : ↥K, ρ ⟨(k : G), hKH k.2⟩ = ι k) (hK : Nat.card K = 360)
    {E₁ E₂ : Subgroup G} (h₁ : E₁ ≤ S ⊓ K) (h₁4 : IsFourSubgroup E₁) (h₂ : E₂ ≤ S ⊓ K)
    (h₂4 : IsFourSubgroup E₂) : ∃ s ∈ S, E₂ = CFSG.conjugate E₁ s := by
  by_cases hE : E₁ = E₂
  · refine ⟨1, S.one_mem, ?_⟩
    rw [← hE]
    ext x
    rw [mem_conjugate_iff']
    simp
  have hconjK : ∀ (h : ↥H) (k : ↥K), (h : G) * k * (h : G)⁻¹ ∈ K := fun h k =>
    (Subgroup.mem_normalizer_iff.mp (hHK h.2) k).mp k.2
  have hρconj : ∀ (h : ↥H) (k : ↥K),
      ρ h * ι k * (ρ h)⁻¹ = ι ⟨(h : G) * k * (h : G)⁻¹, hconjK h k⟩ := by
    intro h k
    rw [← hιρ k, ← hιρ ⟨_, hconjK h k⟩, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext rfl)
  have hPnorm : ∀ a ∈ autA6, ∀ x ∈ psl29, a * x * a⁻¹ ∈ psl29 := by
    intro a ha x hx
    rw [← hρ] at ha
    rw [← hιr] at hx ⊢
    obtain ⟨h, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := hx
    exact ⟨_, (hρconj h k).symm⟩
  have hP : Nat.card psl29 = 360 := by
    have h1 : Nat.card ι.range = Nat.card K :=
      Nat.card_congr (MonoidHom.ofInjective hι).toEquiv.symm
    rw [hιr] at h1
    rw [h1, hK]
  have hR : IsSylowTwoOf ((S.subgroupOf H).map ρ) autA6 := by
    have := isSylowTwoOf_map_range hS ρ
    rwa [hρ] at this
  have hSK2 : IsPGroup 2 ↥(S ⊓ K) := hS.isPGroup.to_le inf_le_left
  have hSKcard : Nat.card ↥(S ⊓ K) = 8 := by
    have hdvd : Nat.card ↥(S ⊓ K) ∣ 360 := hK ▸ Subgroup.card_dvd_of_le inf_le_right
    have hle := card_le_eight_of_dvd hSK2 hdvd
    have hgt : 4 < Nat.card ↥(S ⊓ K) := by
      by_contra hcon
      have hcon' := not_lt.mp hcon
      apply hE
      have e1 : E₁ = S ⊓ K := Subgroup.eq_of_le_of_card_ge h₁ (by rw [h₁4.2]; exact hcon')
      have e2 : E₂ = S ⊓ K := Subgroup.eq_of_le_of_card_ge h₂ (by rw [h₂4.2]; exact hcon')
      rw [e1, e2]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := hSK2.exists_card_eq
    rw [hj] at hle hgt ⊢
    have hj3 : j ≤ 3 := by
      by_contra hcon
      have : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hj3' : 3 ≤ j := by
      by_contra hcon
      have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : j = 3 := le_antisymm hj3 hj3'
    subst this
    norm_num
  set F : Subgroup (Perm (Fin 10)) := ((S ⊓ K).subgroupOf K).map ι with hF
  have hFcard : Nat.card F = 8 := by
    rw [hF, Subgroup.card_map_of_injective hι, ← hSKcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hFP : F ≤ psl29 := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← hιr]
    exact ⟨k, rfl⟩
  have hFR : F ≤ (S.subgroupOf H).map ρ := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨⟨(k : G), hKH k.2⟩, ?_, hιρ k⟩
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hk).1
  let Eimg : Subgroup G → Subgroup (Perm (Fin 10)) := fun E => (E.subgroupOf K).map ι
  have hEimg_le : ∀ {E : Subgroup G}, E ≤ S ⊓ K → Eimg E ≤ F := by
    intro E hE
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hE (Subgroup.mem_subgroupOf.mp hx))
  have hEimg_four : ∀ {E : Subgroup G}, E ≤ S ⊓ K → IsFourSubgroup E →
      IsFourSubgroup (Eimg E) := fun hE hE4 =>
    isFourSubgroup_map hι (isFourSubgroup_subgroupOf (hE.trans inf_le_right) hE4)
  have hEimg_key : ∀ {X Y : Subgroup G}, X ≤ K → Y ≤ K → Eimg X ≤ Eimg Y → X ≤ Y := by
    intro X Y hX hY h x hx
    have hmem : ι ⟨x, hX hx⟩ ∈ Eimg X := ⟨⟨x, hX hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨k, hk, hkx⟩ := h hmem
    have : k = ⟨x, hX hx⟩ := hι hkx
    rw [this] at hk
    exact Subgroup.mem_subgroupOf.mp hk
  have hne : Eimg E₁ ≠ Eimg E₂ := fun h =>
    hE (le_antisymm (hEimg_key (h₁.trans inf_le_right) (h₂.trans inf_le_right) h.le)
      (hEimg_key (h₂.trans inf_le_right) (h₁.trans inf_le_right) h.ge))
  obtain ⟨p, hpR, hp⟩ := exists_swap hPnorm hP hR (le_inf hFR hFP) hFcard (hEimg_le h₁)
    (hEimg_four h₁ h₁4) (hEimg_le h₂) (hEimg_four h₂ h₂4) hne
  obtain ⟨s', hs', rfl⟩ := hpR
  have hsS : (s' : G) ∈ S := Subgroup.mem_subgroupOf.mp hs'
  refine ⟨(s' : G)⁻¹, S.inv_mem hsS, ?_⟩
  have hsK : ∀ e : ↥K, (s' : G) * e * (s' : G)⁻¹ ∈ K := hconjK s'
  ext x
  rw [mem_conjugate_iff']
  simp only [inv_inv]
  constructor
  · intro hx2
    have hxK : x ∈ K := (h₂ hx2).2
    have hmem : ι ⟨x, hxK⟩ ∈ Eimg E₂ := ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.mpr hx2, rfl⟩
    rw [hp] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    obtain ⟨e, he, rfl⟩ := hy
    have h1 : ι ⟨(s' : G) * e * (s' : G)⁻¹, hsK e⟩ = ι ⟨x, hxK⟩ := by
      rw [← hρconj s' e]
      simpa [MulAut.conj_apply] using hyx
    have h3 : (s' : G) * e * (s' : G)⁻¹ = x := congrArg Subtype.val (hι h1)
    have h4 : (s' : G)⁻¹ * x * (s' : G) = (e : G) := by
      rw [← h3]
      group
    rw [h4]
    exact Subgroup.mem_subgroupOf.mp he
  · intro hxe
    have hxK : x ∈ K := by
      have h5 : x = (s' : G) * ((s' : G)⁻¹ * x * (s' : G)) * (s' : G)⁻¹ := by group
      rw [h5]
      exact hsK ⟨_, (h₁ hxe).2⟩
    let e : ↥K := ⟨(s' : G)⁻¹ * x * (s' : G), (h₁ hxe).2⟩
    have h3 : ι ⟨x, hxK⟩ = ρ s' * ι e * (ρ s')⁻¹ := by
      rw [hρconj s' e]
      congr 1
      apply Subtype.ext
      show x = (s' : G) * ((s' : G)⁻¹ * x * (s' : G)) * (s' : G)⁻¹
      group
    have hmem : ι ⟨x, hxK⟩ ∈ (Eimg E₁).map (MulAut.conj (ρ s')).toMonoidHom :=
      ⟨ι e, ⟨e, Subgroup.mem_subgroupOf.mpr hxe, rfl⟩, by simp [MulAut.conj_apply, h3]⟩
    rw [← hp] at hmem
    obtain ⟨k, hk, hkx⟩ := hmem
    have h6 : k = ⟨x, hxK⟩ := hι hkx
    rw [h6] at hk
    exact Subgroup.mem_subgroupOf.mp hk

end CFSG.QuasithinUnique.A6Fusion
