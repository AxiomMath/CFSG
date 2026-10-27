module

public import CFSG.Foundations.KCoreOpen

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

open Subgroup

@[expose] def IsSecOf {A : Type*} [Group A] (U : Subgroup A) (S : Type*) [Group S] : Prop :=
  ∃ H : Subgroup A, H ≤ U ∧ ∃ ψ : H →* S, Function.Surjective ψ

section Basic

variable {A B S : Type*} [Group A] [Group B] [Group S]

theorem IsSecOf.mono {U V : Subgroup A} (hUV : U ≤ V) (h : IsSecOf U S) : IsSecOf V S := by
  obtain ⟨H, hH, ψ, hψ⟩ := h
  exact ⟨H, hH.trans hUV, ψ, hψ⟩

theorem isSecOf_of_surjective {U : Subgroup A} (ψ : U →* S) (hψ : Function.Surjective ψ) :
    IsSecOf U S :=
  ⟨U, le_rfl, ψ, hψ⟩

theorem isSecOf_self (U : Subgroup A) : IsSecOf U U :=
  isSecOf_of_surjective (MonoidHom.id U) Function.surjective_id

theorem IsSecOf.card_dvd [Finite A] {U : Subgroup A} (h : IsSecOf U S) :
    Nat.card S ∣ Nat.card U := by
  obtain ⟨H, hHU, ψ, hψ⟩ := h
  exact (Subgroup.card_dvd_of_surjective (f := ψ) hψ).trans (Subgroup.card_dvd_of_le hHU)

theorem IsSecOf.subgroupOf {W U : Subgroup A} (hUW : U ≤ W) (h : IsSecOf U S) :
    IsSecOf (U.subgroupOf W) S := by
  obtain ⟨H, hHU, ψ, hψ⟩ := h
  have hHW : H ≤ W := hHU.trans hUW
  refine ⟨H.subgroupOf W, fun x hx => Subgroup.mem_subgroupOf.mpr
    (hHU (Subgroup.mem_subgroupOf.mp hx)),
    ψ.comp (Subgroup.subgroupOfEquivOfLe hHW).toMonoidHom, ?_⟩
  exact hψ.comp (Subgroup.subgroupOfEquivOfLe hHW).surjective

theorem IsSecOf.comap (f : A →* B) {V : Subgroup B} (hV : V ≤ f.range) (h : IsSecOf V S) :
    IsSecOf (V.comap f) S := by
  obtain ⟨H, hHV, ψ, hψ⟩ := h
  have hsurj : Function.Surjective (f.subgroupComap H) := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hV (hHV hb)
    exact ⟨⟨a, by simpa [ha] using hb⟩, Subtype.ext ha⟩
  exact ⟨H.comap f, Subgroup.comap_mono hHV, ψ.comp (f.subgroupComap H), hψ.comp hsurj⟩

end Basic

section Quotients

variable {A B S : Type*} [Group A] [Group B] [Group S]

theorem map_ker_eq_top_of_solvable {H Q : Type*} [Group H] [Group Q] [IsSimpleGroup S]
    (hnab : ¬ ∀ a b : S, a * b = b * a) (ψ : H →* S) (hψ : Function.Surjective ψ)
    (g : H →* Q) [Group.IsSolvable Q] : g.ker.map ψ = ⊤ := by
  have hn : (g.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (g.ker.map ψ)) with hbot | htop
  · exfalso
    have hle : g.ker ≤ ψ.ker := by
      intro n hn'
      have : ψ n ∈ g.ker.map ψ := Subgroup.mem_map_of_mem ψ hn'
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    let φ : H ⧸ g.ker →* S := QuotientGroup.lift g.ker ψ hle
    have hφ : Function.Surjective φ := fun s => by
      obtain ⟨h, rfl⟩ := hψ s
      exact ⟨(h : H ⧸ g.ker), rfl⟩
    haveI : Group.IsSolvable (H ⧸ g.ker) :=
      Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective g)
    haveI : Group.IsSolvable S := Group.isSolvable_of_surjective hφ
    exact hnab (IsSimpleGroup.comm_iff_isSolvable.mpr this)
  · exact htop

theorem exists_surjective_inf_of_map_eq_top {H W : Subgroup A} (ψ : H →* S)
    (htop : (W.subgroupOf H).map ψ = ⊤) :
    ∃ ψ' : ↥(H ⊓ W) →* S, Function.Surjective ψ' := by
  refine ⟨ψ.comp (Subgroup.inclusion inf_le_left), fun s => ?_⟩
  have hs : s ∈ (W.subgroupOf H).map ψ := htop ▸ Subgroup.mem_top s
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hs
  exact ⟨⟨(n : A), n.2, Subgroup.mem_subgroupOf.mp hn⟩, rfl⟩

theorem IsSecOf.of_commutator_mem [IsSimpleGroup S] (hnab : ¬ ∀ a b : S, a * b = b * a)
    {U W : Subgroup A} (hWU : W ≤ U) (hc : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ W)
    (h : IsSecOf U S) : IsSecOf W S := by
  obtain ⟨H, hHU, ψ, hψ⟩ := h
  haveI hN : (W.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := W.mul_mem (hc (g : A) (hHU g.2) (n : A) (hWU hn)) hn
    simpa [mul_assoc] using this⟩
  haveI : Group.IsSolvable (↥H ⧸ W.subgroupOf H) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have := hc ((b : A)⁻¹) (hHU (H.inv_mem b.2)) ((a : A)⁻¹) (hHU (H.inv_mem a.2))
    simpa [mul_assoc] using this
  have htop := map_ker_eq_top_of_solvable hnab ψ hψ (QuotientGroup.mk' (W.subgroupOf H))
  rw [QuotientGroup.ker_mk'] at htop
  obtain ⟨ψ', hψ'⟩ := exists_surjective_inf_of_map_eq_top ψ htop
  exact ⟨H ⊓ W, inf_le_right, ψ', hψ'⟩

theorem IsSecOf.ker_of_solvable [IsSimpleGroup S] (hnab : ¬ ∀ a b : S, a * b = b * a)
    {Q : Type*} [Group Q] [Group.IsSolvable Q] (f : A →* Q) {U : Subgroup A}
    (h : IsSecOf U S) : IsSecOf (f.ker ⊓ U) S := by
  obtain ⟨H, hHU, ψ, hψ⟩ := h
  have htop := map_ker_eq_top_of_solvable hnab ψ hψ (f.comp H.subtype)
  rw [← MonoidHom.comap_ker] at htop
  obtain ⟨ψ', hψ'⟩ := exists_surjective_inf_of_map_eq_top (W := f.ker) ψ htop
  exact ⟨H ⊓ f.ker, fun x hx => ⟨hx.2, hHU hx.1⟩, ψ', hψ'⟩

theorem IsSecOf.map_hom [IsSimpleGroup S] {p : ℕ} (f : A →* B) {U : Subgroup A}
    (hp : p ∣ Nat.card S) (hker : ¬ p ∣ Nat.card (f.ker ⊓ U : Subgroup A))
    (hnab : ¬ ∀ a b : S, a * b = b * a) (h : IsSecOf U S) : IsSecOf (U.map f) S := by
  obtain ⟨H, hHU, ψ, hψ⟩ := h
  set fH : H →* B := f.comp H.subtype with hfH
  have hle : fH.ker ≤ ψ.ker := by
    have hn : (fH.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (fH.ker.map ψ) with hbot | htop
    · intro n hn'
      have : ψ n ∈ fH.ker.map ψ := Subgroup.mem_map_of_mem ψ hn'
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have hsurj : Function.Surjective (ψ.comp fH.ker.subtype) := by
        intro s
        have hs : s ∈ fH.ker.map ψ := htop ▸ Subgroup.mem_top s
        obtain ⟨n, hn', rfl⟩ := Subgroup.mem_map.mp hs
        exact ⟨⟨n, hn'⟩, rfl⟩
      have h1 : Nat.card S ∣ Nat.card fH.ker :=
        Subgroup.card_dvd_of_surjective (f := ψ.comp fH.ker.subtype) hsurj
      have hmap : fH.ker.map H.subtype ≤ f.ker ⊓ U := by
        rintro _ ⟨n, hn', rfl⟩
        exact ⟨MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hn'), hHU n.2⟩
      have h2 : Nat.card fH.ker ∣ Nat.card (f.ker ⊓ U : Subgroup A) := by
        rw [← Subgroup.card_map_of_injective H.subtype_injective]
        exact Subgroup.card_dvd_of_le hmap
      exact hker (hp.trans (h1.trans h2))
  let e := QuotientGroup.quotientKerEquivRange fH
  let ψbar : H ⧸ fH.ker →* S := QuotientGroup.lift fH.ker ψ hle
  have hψbar : Function.Surjective ψbar := fun s => by
    obtain ⟨h, rfl⟩ := hψ s
    exact ⟨(h : H ⧸ fH.ker), rfl⟩
  refine ⟨fH.range, ?_, ψbar.comp e.symm.toMonoidHom, hψbar.comp e.symm.surjective⟩
  rintro _ ⟨h, rfl⟩
  exact ⟨h.1, hHU h.2, rfl⟩

theorem IsSecOf.not_isSolvable [IsSimpleGroup S] (hnab : ¬ ∀ a b : S, a * b = b * a)
    (h : IsSecOf (⊤ : Subgroup A) S) : ¬ Group.IsSolvable A := by
  intro hA
  obtain ⟨H, -, ψ, hψ⟩ := h
  haveI : Group.IsSolvable H := inferInstance
  haveI : Group.IsSolvable S := Group.isSolvable_of_surjective hψ
  exact hnab (IsSimpleGroup.comm_iff_isSolvable.mpr this)

end Quotients

section Catalog

theorem IsSecOf.isCatalogGroup {A S : Type*} [Group A] [Group S] [IsSimpleGroup S]
    (hn : ∃ a b : S, a * b ≠ b * a) (hA : CFSG.Open.IsKGroup A)
    (h : IsSecOf (⊤ : Subgroup A) S) : CFSG.Open.IsCatalogGroup S := by
  obtain ⟨H, -, ψ, hψ⟩ := h
  exact CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hA H hn ψ hψ

end Catalog

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613
