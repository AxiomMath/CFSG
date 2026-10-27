module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41UA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem l41_uy_Y_le_V (h : L41GPh11 t L S x₁ x₂ lam rho) :
    l41Y t x₁ x₂ rho ≤ l41V S t x₁ x₂ := by
  obtain ⟨F', hF'R, -, -, -, -, -, hY⟩ := h.yfacts.exists_F
  have hYR : l41Y t x₁ x₂ rho ≤ l41R t x₁ x₂ rho := by
    rw [hY]
    exact sup_le h.rfacts.fourGrp_le hF'R
  have hRO : l41R t x₁ x₂ rho ≤ l41O2 t x₁ x₂ := by
    rw [h.rfacts.O2_eq]
    exact le_sup_left
  exact hYR.trans (hRO.trans (le_sup_left : l41O2 t x₁ x₂ ≤ l41O2 t x₁ x₂ ⊔ S))

theorem l41_uy_unique (h : L41GPh11 t L S x₁ x₂ lam rho) {W' Y₁ : Subgroup G}
    (hW'p : IsPGroup 2 W') (hVW' : l41V S t x₁ x₂ ≤ W') (hY₁n : NormalIn Y₁ W')
    (hY₁e : CFSG.Open.IsElemAbelian 2 Y₁) (hY₁c : Nat.card Y₁ = 16) :
    Y₁ = l41Y t x₁ x₂ rho := by
  have hSV : S ≤ l41V S t x₁ x₂ := le_sup_right
  have hSW' : S ≤ W' := hSV.trans hVW'
  have hcent : invCent t ⊓ W' = S :=
    eq_of_isPGroup_of_odd_relIndex (H := invCent t)
      (fun s hs => ⟨h.toCtx0.le_invCent hs, hSW' hs⟩) inf_le_left
      (hW'p.to_le inf_le_right) h.toCtx0.relIndex_odd
  have htS : t ∈ S := l41_e8_t_mem_S h.toL41GPh1
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have hfour : 4 ≤ Nat.card ↥(Y₁ ⊓ centralizer ({t} : Set G)) :=
    l41_four_le_card_inf_cent_of_card_sixteen hY₁e hY₁c
      (fun e he => hY₁n.2 t (hSW' htS) e he) ht2
  have hno : ∀ g : G, ∀ e ∈ Y₁, g * t * g⁻¹ ≠ e := by
    intro g e he hge
    refine l41_no_e16_cent_conj h.toL41GPh1 hY₁e hY₁c g ?_
    intro y hy
    rw [hge, Subgroup.mem_centralizer_singleton_iff]
    exact l41_e8_comm hY₁e hy he
  have d : L41EData t S W' Y₁ := ⟨hSW', hcent, hY₁n, hY₁e, hfour, hno⟩
  have hY₁N : Y₁ ≤ l41N t x₁ x₂ := d.le_N h.toL41GPh2
  have hVeq : W' ⊓ l41N t x₁ x₂ = l41V S t x₁ x₂ :=
    eq_of_isPGroup_of_odd_relIndex (H := l41N t x₁ x₂)
      (le_inf hVW' h.normalizerFacts.V_le) inf_le_right (hW'p.to_le inf_le_left)
      h.normalizerFacts.V_sylow
  have hY₁V : Y₁ ≤ l41V S t x₁ x₂ := fun e he => by
    rw [← hVeq]
    exact ⟨hY₁n.1 he, hY₁N he⟩
  exact h.yfacts.E16_V Y₁ ⟨hY₁V, hY₁e, hY₁c⟩

theorem l41_uy_normal (h : L41GPh11 t L S x₁ x₂ lam rho) {W' : Subgroup G}
    (hW'p : IsPGroup 2 W') (hVW' : l41V S t x₁ x₂ ≤ W') :
    NormalIn (l41Y t x₁ x₂ rho) W' := by
  have hYV := l41_uy_Y_le_V h
  have hYW' : l41Y t x₁ x₂ rho ≤ W' := hYV.trans hVW'
  haveI hchar := h.yfacts.char_Y
  have hYVn : ((l41Y t x₁ x₂ rho).subgroupOf (l41V S t x₁ x₂)).Normal := inferInstance
  have hVN : ∀ k ∈ l41V S t x₁ x₂, ∀ y ∈ l41Y t x₁ x₂ rho,
      k * y * k⁻¹ ∈ l41Y t x₁ x₂ rho := fun k hk y hy =>
    (Subgroup.normal_subgroupOf_iff hYV).mp hYVn y k hy hk
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G,
      K = W' ⊓ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) := ⟨_, rfl⟩
  have hKmem : ∀ x, x ∈ K ↔
      x ∈ W' ∧ x ∈ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) := fun x => by
    rw [hK]
    exact Subgroup.mem_inf
  have hKW' : K ≤ W' := fun x hx => ((hKmem x).mp hx).1
  have hVK : l41V S t x₁ x₂ ≤ K := fun v hv =>
    (hKmem v).mpr ⟨hVW' hv, mem_normalizer_of_conj_mem (fun y hy => hVN v hv y hy)⟩
  have hYK : l41Y t x₁ x₂ rho ≤ K := hYV.trans hVK
  have hKN : ∀ k ∈ K, ∀ y ∈ l41Y t x₁ x₂ rho, k * y * k⁻¹ ∈ l41Y t x₁ x₂ rho :=
    fun k hk y hy => (Subgroup.mem_set_normalizer_iff.mp ((hKmem k).mp hk).2 y).mp hy
  have hKeq : K = W' := by
    by_contra hne
    have hlt : K < W' := lt_of_le_of_ne hKW' hne
    obtain ⟨w, hwW', hwK, hwnot⟩ := exists_mem_normalizer_not_mem hW'p hlt
    have hwK' : ∀ x, x ∈ K ↔ w * x * w⁻¹ ∈ K := Subgroup.mem_set_normalizer_iff.mp hwK
    obtain ⟨Yw, hYw⟩ : ∃ Yw : Subgroup G,
        Yw = (l41Y t x₁ x₂ rho).map (MulAut.conj w).toMonoidHom := ⟨_, rfl⟩
    have hYwmem : ∀ x, x ∈ Yw ↔ ∃ y ∈ l41Y t x₁ x₂ rho, w * y * w⁻¹ = x := fun x => by
      rw [hYw]
      simp [Subgroup.mem_map, MulAut.conj_apply]
    have hYwK : NormalIn Yw K := by
      refine ⟨?_, ?_⟩
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := (hYwmem x).mp hx
        exact (hwK' y).mp (hYK hy)
      · intro k hk x hx
        obtain ⟨y, hy, rfl⟩ := (hYwmem x).mp hx
        have hk' : w⁻¹ * k * w ∈ K := by
          refine (hwK' (w⁻¹ * k * w)).mpr ?_
          have e : w * (w⁻¹ * k * w) * w⁻¹ = k := by group
          rw [e]
          exact hk
        refine (hYwmem _).mpr ⟨(w⁻¹ * k * w) * y * (w⁻¹ * k * w)⁻¹, hKN _ hk' y hy, ?_⟩
        group
    have hYwe : CFSG.Open.IsElemAbelian 2 Yw := by
      rw [hYw]
      exact h.yfacts.Y_elem.1.map (MulAut.conj w).toMonoidHom
    have hYwc : Nat.card Yw = 16 := by
      rw [hYw, Subgroup.card_map_of_injective (MulAut.conj w).injective]
      exact h.yfacts.Y_elem.2
    have hYweq : Yw = l41Y t x₁ x₂ rho :=
      l41_uy_unique h (hW'p.to_le hKW') hVK hYwK hYwe hYwc
    have hwN : w ∈ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
      refine mem_normalizer_of_conj_mem (fun y hy => ?_)
      have hmem : w * y * w⁻¹ ∈ Yw := (hYwmem _).mpr ⟨y, hy, rfl⟩
      rwa [hYweq] at hmem
    exact hwnot ((hKmem w).mpr ⟨hwW', hwN⟩)
  refine ⟨hYW', fun g hg k hk => ?_⟩
  have hgN : g ∈ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) :=
    ((hKmem g).mp (hKeq ▸ hg)).2
  exact (Subgroup.mem_set_normalizer_iff.mp hgN k).mp hk

theorem l41_uy_odd_index (h : L41GPh11 t L S x₁ x₂ lam rho) :
    ¬ 2 ∣ (normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G)).index := by
  obtain ⟨𝒮, h𝒮⟩ := h.normalizerFacts.V_pGroup.exists_le_sylow
  have hn := l41_uy_normal h (show IsPGroup 2 (𝒮 : Subgroup G) from 𝒮.isPGroup') h𝒮
  have hle : (𝒮 : Subgroup G) ≤ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_of_conj_mem (fun y hy => hn.2 g hg y hy)
  exact fun h2 => 𝒮.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hle))

theorem l41_uy_of (h : L41GPh11 t L S x₁ x₂ lam rho) : L41UniqueYFact t S x₁ x₂ rho :=
  ⟨fun _ hW'p hVW' => ⟨l41_uy_normal h hW'p hVW', fun _ hY₁n hY₁e hY₁c =>
    l41_uy_unique h hW'p hVW' hY₁n hY₁e hY₁c⟩, l41_uy_odd_index h⟩

end S4A

theorem l41_uniqueY_holds : L41UniqueYStmt :=
  fun h => S4A.l41_uy_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
