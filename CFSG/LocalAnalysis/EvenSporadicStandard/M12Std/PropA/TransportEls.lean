module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.TransportJ

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

variable {G P : Type*} [Group G] [Group P] {L : Subgroup G} {t x : G} {K D : Subgroup P}
  {t₀ x₀ : P} {ι : ↥(centralizer ({t} : Set G)) →* P}

theorem IsEmb.G3 (hE : IsEmb L t x K D t₀ x₀ ι) (M : Model K D t₀ x₀) :
    ∃ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G),
      ∃ y ∈ centralizer (jOf L x : Set G) ⊓
        (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)), c * y * c⁻¹ * y⁻¹ = x := by
  have hDK : D ≤ K := M.D_le
  have hx0 : ι ⟨x, hE.x_mem_C⟩ = x₀ := hE.map_x _ rfl
  have hJ_C : jOf L x ≤ centralizer ({t} : Set G) := hE.J_le.trans inf_le_right
  have hpushCx : push ι (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) =
      centralizer ({x₀} : Set P) ⊓ ι.range := by
    rw [push_inf hE.inj, push_centralizer_singleton hE.inj hE.x_mem_C,
      push_self ι, hx0, inf_assoc, inf_idem]
  have hKx : K ⊓ centralizer ({x₀} : Set P) =
      push ι (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G)) := by
    rw [hpushCx, hE.range_eq, inf_comm]
  have hY : centralizer (jOf D x₀ : Set P) ⊓ (K ⊓ centralizer ({x₀} : Set P)) =
      push ι (centralizer (jOf L x : Set G) ⊓
        (centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G))) := by
    rw [push_inf hE.inj, push_centralizer hE.inj hJ_C, hpushCx,
      hE.push_jOf hDK, hE.range_eq]
    simp only [inf_assoc, inf_left_comm, inf_comm, inf_idem, inf_left_idem, inf_right_idem]
  obtain ⟨c₀, hc₀, y₀, hy₀, hcy⟩ := M.G3
  rw [hKx] at hc₀
  rw [hY] at hy₀
  obtain ⟨c₁, hc₁, hcι⟩ := (mem_push ι).mp hc₀
  obtain ⟨y₁, hy₁, hyι⟩ := (mem_push ι).mp hy₀
  have hsub : c₁ * y₁ * c₁⁻¹ * y₁⁻¹ = ⟨x, hE.x_mem_C⟩ := by
    apply hE.inj
    simp only [map_mul, map_inv, hcι, hyι, hx0]
    exact hcy
  refine ⟨(c₁ : G), hc₁, (y₁ : G), hy₁, ?_⟩
  simpa using congrArg Subtype.val hsub

theorem IsEmb.G5 (hE : IsEmb L t x K D t₀ x₀ ι) (M : Model K D t₀ x₀) :
    ∀ z ∈ jOf L x, z ≠ 1 → z * z = 1 →
      ∃ k ∈ L, k * x * k⁻¹ = x * z ∧ jOf L x ⊔ (jOf L x).map (MulAut.conj k).toMonoidHom = L := by
  intro z hzJ hzne hzsq
  have hDK : D ≤ K := M.D_le
  have hx0 : ι ⟨x, hE.x_mem_C⟩ = x₀ := hE.map_x _ rfl
  have hJ_C : jOf L x ≤ centralizer ({t} : Set G) := hE.J_le.trans inf_le_right
  have hzC : z ∈ centralizer ({t} : Set G) := hJ_C hzJ
  have hz₀mem : ι ⟨z, hzC⟩ ∈ jOf D x₀ := by
    have h : ι ⟨z, hzC⟩ ∈ push ι (jOf L x) :=
      (mem_push ι).mpr ⟨⟨z, hzC⟩, hzJ, rfl⟩
    rwa [hE.push_jOf hDK] at h
  have hz₀ne : ι ⟨z, hzC⟩ ≠ 1 := by
    intro h
    apply hzne
    have hz1 : (⟨z, hzC⟩ : ↥(centralizer ({t} : Set G))) = 1 :=
      hE.inj (by simpa using h)
    simpa using congrArg Subtype.val hz1
  have hz₁sq : (⟨z, hzC⟩ : ↥(centralizer ({t} : Set G))) * ⟨z, hzC⟩ = 1 := by
    apply Subtype.ext
    simpa using hzsq
  have hz₀sq : ι ⟨z, hzC⟩ * ι ⟨z, hzC⟩ = 1 := by
    rw [← map_mul, hz₁sq, map_one]
  obtain ⟨k₀, hk₀D, hk₀eq, hk₀sup⟩ := M.G5 (ι ⟨z, hzC⟩) hz₀mem hz₀ne hz₀sq
  have hk₀push : k₀ ∈ push ι L := by
    rw [hE.push_L]; exact hk₀D
  obtain ⟨k₁, hk₁L, hk₁ι⟩ := (mem_push ι).mp hk₀push
  have hk₁C : (k₁ : G) ∈ centralizer ({t} : Set G) := hE.L_le hk₁L
  have hksub : k₁ * ⟨x, hE.x_mem_C⟩ * k₁⁻¹ = ⟨x, hE.x_mem_C⟩ * ⟨z, hzC⟩ := by
    apply hE.inj
    simp only [map_mul, map_inv, hk₁ι, hx0]
    exact hk₀eq
  have hJk_C : (jOf L x).map (MulAut.conj (k₁ : G)).toMonoidHom ≤
      centralizer ({t} : Set G) := by
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨b, hbJ, rfl⟩
    show (k₁ : G) * b * (k₁ : G)⁻¹ ∈ centralizer ({t} : Set G)
    exact mul_mem (mul_mem hk₁C (hJ_C hbJ)) (inv_mem hk₁C)
  have hsupC : jOf L x ⊔ (jOf L x).map (MulAut.conj (k₁ : G)).toMonoidHom ≤
      centralizer ({t} : Set G) := sup_le hJ_C hJk_C
  have hk₁ι' : ι ⟨(k₁ : G), hk₁C⟩ = k₀ := by
    have h : (⟨(k₁ : G), hk₁C⟩ : ↥(centralizer ({t} : Set G))) = k₁ := Subtype.ext rfl
    rw [h, hk₁ι]
  have hpush_eq : push ι (jOf L x ⊔ (jOf L x).map (MulAut.conj (k₁ : G)).toMonoidHom) =
      push ι L := by
    rw [push_sup ι hJ_C hJk_C, push_map_conj ι hk₁C hJ_C, hE.push_jOf hDK,
      hk₁ι', hk₀sup, hE.push_L]
  have hsup : jOf L x ⊔ (jOf L x).map (MulAut.conj (k₁ : G)).toMonoidHom = L :=
    push_injective_of_le hE.inj hsupC hE.L_le hpush_eq
  exact ⟨(k₁ : G), hk₁L, by simpa using congrArg Subtype.val hksub, hsup⟩

theorem IsEmb.G1 (hE : IsEmb L t x K D t₀ x₀ ι) (M : Model K D t₀ x₀) :
    ∀ w ∈ centralizer ({t} : Set G), orderOf w = 2 → w ≠ t →
      ∃ c ∈ centralizer ({t} : Set G), c * w * c⁻¹ ∈ centralizer ({x} : Set G) ∧
        c * w * c⁻¹ ∉ centralizer (jOf L x : Set G) := by
  intro w hwC hword hwne
  have hDK : D ≤ K := M.D_le
  have hx0 : ι ⟨x, hE.x_mem_C⟩ = x₀ := hE.map_x _ rfl
  have hJ_C : jOf L x ≤ centralizer ({t} : Set G) := hE.J_le.trans inf_le_right
  have htC : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hw₀K : ι ⟨w, hwC⟩ ∈ K := by
    rw [← hE.range_eq]
    exact MonoidHom.mem_range.mpr ⟨⟨w, hwC⟩, rfl⟩
  have hw₀ord : orderOf (ι ⟨w, hwC⟩) = 2 := by
    rw [orderOf_injective ι hE.inj ⟨w, hwC⟩, Subgroup.orderOf_mk, hword]
  have hw₀ne : ι ⟨w, hwC⟩ ≠ t₀ := by
    intro h
    apply hwne
    have ht₁ : (⟨t, htC⟩ : ↥(centralizer ({t} : Set G))) = ⟨w, hwC⟩ := by
      apply hE.inj
      rw [h, hE.map_t ⟨t, htC⟩ rfl]
    simpa using congrArg Subtype.val ht₁.symm
  obtain ⟨c₀, hc₀K, hc₀mem, hc₀notmem⟩ := M.G1 (ι ⟨w, hwC⟩) hw₀K hw₀ord hw₀ne
  have hc₀range : c₀ ∈ ι.range := by rwa [← hE.range_eq] at hc₀K
  obtain ⟨c₁, hc₁ι⟩ := MonoidHom.mem_range.mp hc₀range
  have heq : ι (c₁ * ⟨w, hwC⟩ * c₁⁻¹) = c₀ * ι ⟨w, hwC⟩ * c₀⁻¹ := by
    simp only [map_mul, map_inv, hc₁ι]
  have hc₁mem : ι (c₁ * ⟨w, hwC⟩ * c₁⁻¹) ∈ centralizer ({x₀} : Set P) := by
    rw [heq]; exact hc₀mem
  have hu1_comm : (c₁ * ⟨w, hwC⟩ * c₁⁻¹) * ⟨x, hE.x_mem_C⟩ =
      ⟨x, hE.x_mem_C⟩ * (c₁ * ⟨w, hwC⟩ * c₁⁻¹) := by
    apply hE.inj
    simp only [map_mul, map_inv, hx0, hc₁ι]
    simpa only [heq] using mem_centralizer_singleton_iff.mp hc₁mem
  have hu_comm : (c₁ : G) * w * (c₁ : G)⁻¹ * x =
      x * ((c₁ : G) * w * (c₁ : G)⁻¹) := by
    simpa using congrArg Subtype.val hu1_comm
  have hc_mem_x : (c₁ : G) * w * (c₁ : G)⁻¹ ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr hu_comm
  have hc_notmem_J : (c₁ : G) * w * (c₁ : G)⁻¹ ∉ centralizer (jOf L x : Set G) := by
    intro hmem
    apply hc₀notmem
    have h : ι (c₁ * ⟨w, hwC⟩ * c₁⁻¹) ∈ push ι (centralizer (jOf L x : Set G)) :=
      (mem_push ι).mpr ⟨c₁ * ⟨w, hwC⟩ * c₁⁻¹, hmem, rfl⟩
    rw [push_centralizer hE.inj hJ_C, hE.push_jOf hDK, hE.range_eq, heq] at h
    exact h.1
  exact ⟨(c₁ : G), c₁.prop, hc_mem_x, hc_notmem_J⟩

theorem IsEmb.G2 (hE : IsEmb L t x K D t₀ x₀ ι) (M : Model K D t₀ x₀) :
    ∀ x' ∈ centralizer ({t} : Set G), orderOf x' = 2 →
      Nat.card ↥(centralizer ({x'} : Set G) ⊓ centralizer ({t} : Set G)) ∣ 960 →
      ∃ R : Subgroup G, R ≤ centralizer ({x'} : Set G) ⊓ centralizer ({t} : Set G) ∧
        ⁅R, R⁆ = R ∧ 60 ≤ Nat.card ↥R := by
  intro x' hx'C hx'ord hdvd
  have hJ_C : jOf L x ≤ centralizer ({t} : Set G) := hE.J_le.trans inf_le_right
  have hpushCx' : push ι (centralizer ({x'} : Set G) ⊓ centralizer ({t} : Set G)) =
      centralizer ({ι ⟨x', hx'C⟩} : Set P) ⊓ ι.range := by
    rw [push_inf hE.inj, push_centralizer_singleton hE.inj hx'C, push_self ι,
      inf_assoc, inf_idem]
  have hKx' : K ⊓ centralizer ({ι ⟨x', hx'C⟩} : Set P) =
      push ι (centralizer ({x'} : Set G) ⊓ centralizer ({t} : Set G)) := by
    rw [hpushCx', hE.range_eq, inf_comm]
  have hx'0K : ι ⟨x', hx'C⟩ ∈ K := by
    rw [← hE.range_eq]
    exact MonoidHom.mem_range.mpr ⟨⟨x', hx'C⟩, rfl⟩
  have hx'0ord : orderOf (ι ⟨x', hx'C⟩) = 2 := by
    rw [orderOf_injective ι hE.inj ⟨x', hx'C⟩, Subgroup.orderOf_mk, hx'ord]
  have hdvd' : Nat.card ↥(K ⊓ centralizer ({ι ⟨x', hx'C⟩} : Set P)) ∣ 960 := by
    rw [hKx', card_push hE.inj (H := centralizer ({x'} : Set G) ⊓
      centralizer ({t} : Set G)) inf_le_right]
    exact hdvd
  obtain ⟨R₀, hR₀le, hR₀comm, hR₀card⟩ :=
    M.G2 (ι ⟨x', hx'C⟩) hx'0K hx'0ord hdvd'
  let R : Subgroup G := (R₀.comap ι).map (centralizer ({t} : Set G)).subtype
  have hR_C : R ≤ centralizer ({t} : Set G) := Subgroup.map_subtype_le (R₀.comap ι)
  have hRmap : R = (R₀.comap ι).map (centralizer ({t} : Set G)).subtype := rfl
  have hR₀leK : R₀ ≤ K := hR₀le.trans inf_le_left
  have hR₀range : R₀ ≤ ι.range := by rw [hE.range_eq]; exact hR₀leK
  have hpushR : push ι R = R₀ := by
    apply le_antisymm
    · intro p hp
      rcases (mem_push ι).mp hp with ⟨c, hcR, hcp⟩
      rw [hRmap] at hcR
      rcases Subgroup.mem_map.mp hcR with ⟨d, hd, hdc⟩
      have hdc' : d = c := Subtype.ext hdc
      rw [← hcp, ← hdc']
      exact hd
    · intro p hp
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (hR₀range hp)
      have hcR : (c : G) ∈ R := by
        rw [hRmap]
        exact Subgroup.mem_map.mpr ⟨c, by rwa [Subgroup.mem_comap, hc], rfl⟩
      exact (mem_push ι).mpr ⟨c, hcR, hc⟩
  have hle : push ι R ≤ push ι (centralizer ({x'} : Set G) ⊓
      centralizer ({t} : Set G)) := by
    rw [hpushR, ← hKx']
    exact hR₀le
  have hRle : R ≤ centralizer ({x'} : Set G) ⊓ centralizer ({t} : Set G) :=
    (push_le_push_iff hE.inj hR_C).mp hle
  have hcomm_le_R : ⁅R, R⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
  have hcommC : ⁅R, R⁆ ≤ centralizer ({t} : Set G) := hcomm_le_R.trans hR_C
  have hpush_comm : push ι ⁅R, R⁆ = push ι R := by
    rw [push_commutator ι hR_C hR_C, hpushR, hR₀comm]
  have hcomm : ⁅R, R⁆ = R := push_injective_of_le hE.inj hcommC hR_C hpush_comm
  have hcardR : Nat.card ↥R₀ = Nat.card ↥R := by
    have h := card_push hE.inj hR_C
    rwa [hpushR] at h
  have h60R : 60 ≤ Nat.card ↥R := by rw [← hcardR]; exact hR₀card
  exact ⟨R, hRle, hcomm, h60R⟩

end CFSG.EvenSporadicStandard.M12Std.PropA
