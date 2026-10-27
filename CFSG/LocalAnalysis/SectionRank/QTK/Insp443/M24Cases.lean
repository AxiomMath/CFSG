module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24Ident
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24IdentTrio
public import CFSG.Quasithin.Vol2.KGFactC31M24

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M24 CFSG.SectionRank.QTK.Insp443.M24

private theorem conj_comp (a b : G₀) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem m24_frame
    {L V MK : Subgroup G₀} (h : KConfig G₀ L V MK)
    {y t g c : G₀} (hy : y ∈ L) (ht : t ∈ V) (hyk : ∃ k, y ^ 7 ^ k = 1) (hy1 : y ≠ 1)
    (hx7 : MulAut.conj g x7 ∈ Subgroup.zpowers y)
    (hframe : ∀ {v : G₀}, v ∈ Subgroup.centralizer
        (((eSub basis_u5).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀) →
      v ∉ (eSub basis_u5).map (MulAut.conj c).toMonoidHom →
      (∀ a ∈ (eSub basis_u5).map (MulAut.conj c).toMonoidHom ⊔ orbSub x7 v,
        ∀ b ∈ (eSub basis_u5).map (MulAut.conj c).toMonoidHom ⊔ orbSub x7 v, a * b = b * a) →
      (∀ a ∈ (eSub basis_u5).map (MulAut.conj c).toMonoidHom ⊔ orbSub x7 v, a * a = 1) →
      (∃ e : G₀, (eSub basis_u5).map (MulAut.conj c).toMonoidHom ⊔ orbSub x7 v =
          (eSub basis_o).map (MulAut.conj e).toMonoidHom) ∨
        ∃ e : G₀, (eSub basis_u5).map (MulAut.conj c).toMonoidHom ⊔ orbSub x7 v =
          (eSub basis_t).map (MulAut.conj e).toMonoidHom)
    (hU : orbSub y t = ((eSub basis_u5).map (MulAut.conj c).toMonoidHom).map
      (MulAut.conj g).toMonoidHom) :
    (V = (eSub basis_u5).map (MulAut.conj (g * c)).toMonoidHom ∧
        L = Lq.map (MulAut.conj (g * c)).toMonoidHom) ∨
      (∃ e : G₀, V = (eSub basis_o).map (MulAut.conj (g * e)).toMonoidHom ∧
        L = Mo.map (MulAut.conj (g * e)).toMonoidHom) ∨
      ∃ e : G₀, V = (eSub basis_et).map (MulAut.conj (g * e * gE⁻¹)).toMonoidHom ∧
        L = Lq.map (MulAut.conj (g * e * gE⁻¹)).toMonoidHom := by
  set U₀ : Subgroup G₀ := (eSub basis_u5).map (MulAut.conj c).toMonoidHom with hU₀
  have hUV : U₀.map (MulAut.conj g).toMonoidHom ≤ V :=
    hU ▸ orbSub_le (h.le_normalizer hy) ht
  have hVC : V ≤ Subgroup.centralizer (V : Set G₀) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr h.elemAbelian.1
  by_cases hVU : V ≤ U₀.map (MulAut.conj g).toMonoidHom
  ·
    have hVeq : V = U₀.map (MulAut.conj g).toMonoidHom := le_antisymm hVU hUV
    have hV5 : V = (eSub basis_u5).map (MulAut.conj (g * c)).toMonoidHom := by
      rw [hVeq, hU₀, Subgroup.map_map, conj_comp g c]
    exact Or.inl ⟨hV5, h.m24_eq_u5 hV5 hy hyk hy1⟩
  ·
    obtain ⟨v, hvV, hvU⟩ := Set.not_subset.mp hVU
    obtain ⟨v₀, rfl⟩ := (MulAut.conj g).surjective v
    have hv₀C : v₀ ∈ Subgroup.centralizer (U₀ : Set G₀) := by
      have h1 : (MulAut.conj g).toMonoidHom v₀ ∈ Subgroup.centralizer
          ((U₀.map (MulAut.conj g).toMonoidHom : Subgroup G₀) : Set G₀) :=
        (Subgroup.centralizer_le hUV) (hVC hvV)
      rw [centralizer_map_conj U₀ g] at h1
      obtain ⟨w, hw, hwf⟩ := h1
      rw [(MulAut.conj g).injective hwf] at hw
      exact hw
    have hv₀U : v₀ ∉ U₀ := fun h' =>
      hvU (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom h')
    have hx7L : MulAut.conj g x7 ∈ L := Subgroup.zpowers_le.mpr hy hx7
    have hWV : (U₀ ⊔ orbSub x7 v₀).map (MulAut.conj g).toMonoidHom ≤ V := by
      rw [Subgroup.map_sup, orbSub_map]
      exact sup_le hUV (orbSub_le (h.le_normalizer hx7L) hvV)
    have hab : ∀ a ∈ U₀ ⊔ orbSub x7 v₀, ∀ b ∈ U₀ ⊔ orbSub x7 v₀, a * b = b * a :=
      fun a ha b hb => (MulAut.conj g).injective (by
        rw [map_mul, map_mul]
        exact congrArg Subtype.val (h.elemAbelian.1.is_comm.comm
          ⟨_, hWV ⟨a, ha, rfl⟩⟩ ⟨_, hWV ⟨b, hb, rfl⟩⟩))
    have hsq : ∀ a ∈ U₀ ⊔ orbSub x7 v₀, a * a = 1 := fun a ha =>
      (MulAut.conj g).injective (by
        rw [map_mul, map_one]
        have := h.elemAbelian.2 ((MulAut.conj g) a) (hWV ⟨a, ha, rfl⟩)
        rwa [sq] at this)
    rcases hframe hv₀C hv₀U hab hsq with ⟨e, he⟩ | ⟨e, he⟩
    ·
      have hle : (eSub basis_o).map (MulAut.conj (g * e)).toMonoidHom ≤ V := by
        have h1 : (eSub basis_o).map
            ((MulAut.conj g).toMonoidHom.comp (MulAut.conj e).toMonoidHom) ≤ V := by
          rw [← Subgroup.map_map, ← he]
          exact hWV
        rwa [conj_comp g e] at h1
      exact Or.inr (Or.inl ⟨e, h.m24_eq_of_o hle⟩)
    ·
      have hle : (eSub basis_t).map (MulAut.conj (g * e)).toMonoidHom ≤ V := by
        have h1 : (eSub basis_t).map
            ((MulAut.conj g).toMonoidHom.comp (MulAut.conj e).toMonoidHom) ≤ V := by
          rw [← Subgroup.map_map, ← he]
          exact hWV
        rwa [conj_comp g e] at h1
      exact Or.inr (Or.inr ⟨e, h.m24_eq_of_t hle hy hyk hy1⟩)

theorem KConfig.m24_cases
    {L V MK : Subgroup G₀} (h : KConfig G₀ L V MK) :
    ∃ g : G₀,
      (V = (eSub basis_o).map (MulAut.conj g).toMonoidHom ∧
        L = Mo.map (MulAut.conj g).toMonoidHom) ∨
      (V = (eSub basis_s).map (MulAut.conj g).toMonoidHom ∧
        L = Ls.map (MulAut.conj g).toMonoidHom) ∨
      (V = (eSub basis_et).map (MulAut.conj g).toMonoidHom ∧
        L = Lq.map (MulAut.conj g).toMonoidHom) ∨
      (V = (eSub basis_u5).map (MulAut.conj g).toMonoidHom ∧
        L = Lq.map (MulAut.conj g).toMonoidHom) := by
  have hne : ⁅V, L⁆ ≠ ⊥ := by rw [← h.eq_commutator]; exact h.ne_bot
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ :=
    exists_pElement_not_comm h.perfect h.le_normalizer hne
  have hy1 : y ≠ 1 := fun h1 => hyt (by rw [h1, one_mul, inv_one, mul_one])
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      have := h.elemAbelian.2 t ht
      rwa [sq] at this
    · intro h1
      apply hyt
      rw [h1, mul_one, mul_inv_cancel]
  have hcommA : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t := fun j => by
    have hm : y ^ j * t * y⁻¹ ^ j ∈ V := by
      rw [inv_pow]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.le_normalizer hy) j) t).mp ht
    have := h.elemAbelian.1.is_comm.comm ⟨t, ht⟩ ⟨_, hm⟩
    simpa using congrArg Subtype.val this
  have hpd : p ∣ 244823040 := by
    by_contra hpd
    have h1 : y = 1 := eq_one_of_pow_of_not_dvd hp
      (by rwa [CFSG.Sporadic.Schreier.m24_card]) ⟨k, hyk⟩
    exact hy1 h1
  have key : ∀ (x : G₀), orderOf x = p → ¬ p ∣ 244823040 / p → ∃ (g y₁ t₁ : G₀),
      y₁ ∈ Subgroup.zpowers x ∧ MulAut.conj g x ∈ Subgroup.zpowers y ∧
        y₁ * t₁ * y₁⁻¹ ≠ t₁ ∧ orderOf t₁ = 2 ∧
        (∀ j : ℕ, t₁ * (y₁ ^ j * t₁ * y₁⁻¹ ^ j) = y₁ ^ j * t₁ * y₁⁻¹ ^ j * t₁) ∧
        orbSub y t = (orbSub x t₁).map (MulAut.conj g).toMonoidHom := by
    intro x hx hpi
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hP, hPi⟩ := sylow_of_order hx hpi
    obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi ⟨k, hyk⟩
    let f : G₀ →* G₀ := (MulAut.conj g).toMonoidHom
    have hf : Function.Injective f := (MulAut.conj g).injective
    have hconj : ∀ z : G₀, f (g⁻¹ * z * g) = z := fun z => by
      change (MulAut.conj g).toMonoidHom (g⁻¹ * z * g) = z
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hfy : f (g⁻¹ * y * g) = y := hconj y
    have hft : f (g⁻¹ * t * g) = t := hconj t
    generalize g⁻¹ * y * g = y₁ at hg hfy
    generalize g⁻¹ * t * g = t₁ at hft
    have hy₁1 : y₁ ≠ 1 := fun h1 => hy1 (by rw [← hfy, h1, map_one])
    have hxy : x ∈ Subgroup.zpowers y₁ := mem_zpowers_of_prime hp hx hg hy₁1
    have hxg : MulAut.conj g x ∈ Subgroup.zpowers y := by
      have h1 : (MulAut.conj g).toMonoidHom x ∈
          (Subgroup.zpowers y₁).map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hxy
      rwa [MonoidHom.map_zpowers, hfy] at h1
    refine ⟨g, y₁, t₁, hg, hxg, fun h => hyt ?_, ?_, fun j => hf ?_, ?_⟩
    · have := congrArg f h
      rwa [map_mul, map_mul, map_inv, hfy, hft] at this
    · rw [← ht2, ← hft, orderOf_injective f hf]
    · simp only [map_mul, map_pow, map_inv, hfy, hft]
      exact hcommA j
    · rw [← orbSub_eq_of_zpowers hg hxy, orbSub_map, hfy, hft]
  rcases prime_dvd_m24 hp hp5 hpd with rfl | rfl | rfl | rfl
  ·
    obtain ⟨g, y₁, t₁, hg, -, hmv, hord, hcm, hU⟩ := key x5 orderOf_x5 (by norm_num)
    have hy₁1 : y₁ ≠ 1 := fun h1 => hmv (by rw [h1, one_mul, inv_one, mul_one])
    have hxy : x5 ∈ Subgroup.zpowers y₁ := mem_zpowers_of_prime hp orderOf_x5 hg hy₁1
    obtain ⟨hmv5, hcm5⟩ := bad_of_zpowers hg hxy hmv hcm
    rcases orbSub_cases5 hord hmv5 (fun j _ => hcm5 j) with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
    · have hle : (eSub basis_s32).map (MulAut.conj (g * c)).toMonoidHom ≤ V := by
        rw [hc, Subgroup.map_map, conj_comp g c] at hU
        exact hU ▸ orbSub_le (h.le_normalizer hy) ht
      exact ⟨g * c, Or.inr (Or.inl (h.m24_eq_of_s32 hle hy ⟨k, hyk⟩ hy1))⟩
    · have hle : (eSub basis_s16).map (MulAut.conj (g * c)).toMonoidHom ≤ V := by
        rw [hc, Subgroup.map_map, conj_comp g c] at hU
        exact hU ▸ orbSub_le (h.le_normalizer hy) ht
      exact ⟨g * c, Or.inr (Or.inl (h.m24_eq_of_s16 hle hy ⟨k, hyk⟩ hy1))⟩
    · have hle : (eSub basis_o).map (MulAut.conj (g * c)).toMonoidHom ≤ V := by
        rw [hc, Subgroup.map_map, conj_comp g c] at hU
        exact hU ▸ orbSub_le (h.le_normalizer hy) ht
      exact ⟨g * c, Or.inl (h.m24_eq_of_o hle)⟩
  ·
    obtain ⟨g, y₁, t₁, hg, hxg, hmv, hord, hcm, hU⟩ := key x7 orderOf_x7 (by norm_num)
    have hy₁1 : y₁ ≠ 1 := fun h1 => hmv (by rw [h1, one_mul, inv_one, mul_one])
    have hxy : x7 ∈ Subgroup.zpowers y₁ := mem_zpowers_of_prime hp orderOf_x7 hg hy₁1
    obtain ⟨hmv7, hcm7⟩ := bad_of_zpowers hg hxy hmv hcm
    rcases orbSub_cases7 hord hmv7 (fun j _ => hcm7 j) with
      ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | hc | hc | hc
    · have hle : (eSub basis_u4).map (MulAut.conj (g * c)).toMonoidHom ≤ V := by
        rw [hc, Subgroup.map_map, conj_comp g c] at hU
        exact hU ▸ orbSub_le (h.le_normalizer hy) ht
      exact (h.m24_not_of_u4 hle hy ⟨k, hyk⟩ hy1).elim
    · have hle : (eSub basis_r2).map (MulAut.conj (g * c)).toMonoidHom ≤ V := by
        rw [hc, Subgroup.map_map, conj_comp g c] at hU
        exact hU ▸ orbSub_le (h.le_normalizer hy) ht
      exact (h.m24_not_of_r2 hle hy ⟨k, hyk⟩ hy1).elim
    · have hle : (eSub basis_o).map (MulAut.conj (g * c)).toMonoidHom ≤ V := by
        rw [hc, Subgroup.map_map, conj_comp g c] at hU
        exact hU ▸ orbSub_le (h.le_normalizer hy) ht
      exact ⟨g * c, Or.inl (h.m24_eq_of_o hle)⟩
    · have hle : (eSub basis_u6).map (MulAut.conj (g * c)).toMonoidHom ≤ V := by
        rw [hc, Subgroup.map_map, conj_comp g c] at hU
        exact hU ▸ orbSub_le (h.le_normalizer hy) ht
      exact ⟨g * c * zE⁻¹,
        Or.inr (Or.inr (Or.inl (h.m24_eq_of_u6 hle hy ⟨k, hyk⟩ hy1)))⟩
    ·
      have hU' : orbSub y t = ((eSub basis_u5).map (MulAut.conj (cand 12)).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by
        rw [hU, hc]
      rcases m24_frame h hy ht ⟨k, hyk⟩ hy1 hxg
        (fun hvC hvU hW hW2 => frame_cases12 hvC hvU hW hW2) hU' with hq | ⟨e, ho⟩ | ⟨e, htrio⟩
      · exact ⟨g * cand 12, Or.inr (Or.inr (Or.inr hq))⟩
      · exact ⟨g * e, Or.inl ho⟩
      · exact ⟨g * e * gE⁻¹, Or.inr (Or.inr (Or.inl htrio))⟩
    ·
      have hU' : orbSub y t = ((eSub basis_u5).map (MulAut.conj (cand 17)).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by
        rw [hU, hc]
      rcases m24_frame h hy ht ⟨k, hyk⟩ hy1 hxg
        (fun hvC hvU hW hW2 => frame_cases17 hvC hvU hW hW2) hU' with hq | ⟨e, ho⟩ | ⟨e, htrio⟩
      · exact ⟨g * cand 17, Or.inr (Or.inr (Or.inr hq))⟩
      · exact ⟨g * e, Or.inl ho⟩
      · exact ⟨g * e * gE⁻¹, Or.inr (Or.inr (Or.inl htrio))⟩
    ·
      have hU' : orbSub y t = ((eSub basis_u5).map (MulAut.conj (cand 18)).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by
        rw [hU, hc]
      rcases m24_frame h hy ht ⟨k, hyk⟩ hy1 hxg
        (fun hvC hvU hW hW2 => frame_cases18 hvC hvU hW hW2) hU' with hq | ⟨e, ho⟩ | ⟨e, htrio⟩
      · exact ⟨g * cand 18, Or.inr (Or.inr (Or.inr hq))⟩
      · exact ⟨g * e, Or.inl ho⟩
      · exact ⟨g * e * gE⁻¹, Or.inr (Or.inr (Or.inl htrio))⟩
  ·
    obtain ⟨g, y₁, t₁, hg, -, hmv, hord, hcm, -⟩ := key x11 orderOf_x11 (by norm_num)
    have hy₁1 : y₁ ≠ 1 := fun h1 => hmv (by rw [h1, one_mul, inv_one, mul_one])
    have hxy : x11 ∈ Subgroup.zpowers y₁ := mem_zpowers_of_prime hp orderOf_x11 hg hy₁1
    obtain ⟨hmv11, hcm11⟩ := bad_of_zpowers hg hxy hmv hcm
    exact (not_bad11 hord hmv11 (fun j _ => hcm11 j)).elim
  ·
    obtain ⟨g, y₁, t₁, hg, -, hmv, hord, hcm, -⟩ := key x23 orderOf_x23 (by norm_num)
    have hy₁1 : y₁ ≠ 1 := fun h1 => hmv (by rw [h1, one_mul, inv_one, mul_one])
    have hxy : x23 ∈ Subgroup.zpowers y₁ := mem_zpowers_of_prime hp orderOf_x23 hg hy₁1
    obtain ⟨hmv23, hcm23⟩ := bad_of_zpowers hg hxy hmv hcm
    exact (not_bad23 hord hmv23 (fun j _ => hcm23 j)).elim

end CFSG.SectionRank.QTK.Insp443

end
