module

public import CFSG.GH74.GLS.C3.Layer2.L5B4
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Transfer
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12 CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] {S : Subgroup G} {M : Type} [Group M]

section Erel

variable (ψ : ↥S ≃* M)

@[expose] def Erel (a b : M) : Prop :=
  IsConj ((ψ.symm a : ↥S) : G) ((ψ.symm b : ↥S) : G)

theorem Erel.equiv : Equivalence (Erel ψ) :=
  ⟨fun _ => IsConj.refl _, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

theorem Erel.conj (a s : M) : Erel ψ a (s * a * s⁻¹) := by
  unfold Erel
  rw [isConj_iff]
  refine ⟨((ψ.symm s : ↥S) : G), ?_⟩
  simp [map_mul, map_inv]

theorem mem_cent_iff {z t : M} :
    z ∈ Subgroup.centralizer ({t} : Set M) ↔
      ((ψ.symm z : ↥S) : G) ∈ Subgroup.centralizer ({((ψ.symm t : ↥S) : G)} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg ψ.symm h
    rw [map_mul, map_mul] at this
    exact congrArg Subtype.val this
  · intro h
    apply ψ.symm.injective
    rw [map_mul, map_mul]
    exact Subtype.ext h

theorem card_cent_eq (t : M) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set M)) =
      Nat.card ↥(S ⊓ Subgroup.centralizer ({((ψ.symm t : ↥S) : G)} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun z => ⟨((ψ.symm z.1 : ↥S) : G), (ψ.symm z.1).2, (mem_cent_iff ψ).1 z.2⟩
      invFun := fun w => ⟨ψ ⟨w.1, w.2.1⟩, ?_⟩
      left_inv := fun z => ?_
      right_inv := fun w => ?_ }
  · rw [mem_cent_iff ψ, MulEquiv.symm_apply_apply]
    exact w.2.2
  · apply Subtype.ext
    simp
  · apply Subtype.ext
    simp

end Erel

section Sylow

variable [Finite G]

theorem card_le_sylow_of_conj {A P : Subgroup G} (hA : IsPGroup 2 ↥A) {u g : G}
    (hAC : A ≤ Subgroup.centralizer ({g * u * g⁻¹} : Set G))
    (hP : IsSylow2In P (Subgroup.centralizer ({u} : Set G))) : Nat.card A ≤ Nat.card P := by
  set B := Hconj g A with hB
  have hBp : IsPGroup 2 ↥B := hA.comap_of_injective _ (MulAut.conj g).injective
  have hBle : B ≤ Subgroup.centralizer ({u} : Set G) := by
    intro b hb
    have hb' : g * b * g⁻¹ ∈ Subgroup.centralizer ({g * u * g⁻¹} : Set G) := hAC hb
    rw [Subgroup.mem_centralizer_singleton_iff] at hb' ⊢
    have h1 : g * b * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * b * g⁻¹) := hb'
    have h2 : b * u = u * b := by
      have : g * (b * u) * g⁻¹ = g * (u * b) * g⁻¹ := by
        calc g * (b * u) * g⁻¹ = g * b * g⁻¹ * (g * u * g⁻¹) := by group
          _ = g * u * g⁻¹ * (g * b * g⁻¹) := h1
          _ = g * (u * b) * g⁻¹ := by group
      simpa using this
    exact h2
  obtain ⟨P', hP', hBP'⟩ := exists_sylow2_ge hBp hBle
  calc Nat.card A = Nat.card B := (Hconj_card g A).symm
    _ ≤ Nat.card P' := Subgroup.card_le_of_le hBP'
    _ = Nat.card P := sylow2_card_eq hP' hP

theorem isExtremal_of_max (hS : IsSylow2In S ⊤) (ψ : ↥S ≃* M) {t' : M}
    (hext : ∀ t'' : M, Erel ψ t' t'' →
      Nat.card ↥(Subgroup.centralizer ({t''} : Set M)) ≤
        Nat.card ↥(Subgroup.centralizer ({t'} : Set M))) :
    IsExtremal S ((ψ.symm t' : ↥S) : G) := by
  set u' : G := ((ψ.symm t' : ↥S) : G) with hu'
  have hSp : IsPGroup 2 ↥S := hS.2.1
  set P := S ⊓ Subgroup.centralizer ({u'} : Set G) with hPdef
  have hPp : IsPGroup 2 ↥P := hSp.to_le inf_le_left
  obtain ⟨Q, hQ, hPQ⟩ := exists_sylow2_ge hPp
    (inf_le_right : P ≤ Subgroup.centralizer ({u'} : Set G))
  have hu'P : u' ∈ P := ⟨(ψ.symm t').2, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hu'Q : u' ∈ Q := hPQ hu'P
  obtain ⟨S', hS', hQS'⟩ := exists_sylow2_ge hQ.2.1 (le_top : Q ≤ ⊤)
  obtain ⟨c0, -, hc0⟩ := sylow2_exists_conj hS' hS
  have hmemS : ∀ a : G, a ∈ S ↔ c0 * a * c0⁻¹ ∈ S' := fun a => by
    have := Subgroup.ext_iff.1 hc0 a
    exact this
  have hu''S : c0⁻¹ * u' * c0 ∈ S := by
    rw [hmemS]
    have : c0 * (c0⁻¹ * u' * c0) * c0⁻¹ = u' := by group
    rw [this]
    exact hQS' hu'Q
  set t'' : M := ψ ⟨c0⁻¹ * u' * c0, hu''S⟩ with ht''
  have hψ : ((ψ.symm t'' : ↥S) : G) = c0⁻¹ * u' * c0 := by simp [ht'']
  have hE : Erel ψ t' t'' := by
    unfold Erel
    rw [hψ, isConj_iff]
    exact ⟨c0⁻¹, by simp [hu', mul_assoc]⟩
  have h1 := hext t'' hE
  rw [card_cent_eq ψ t'', card_cent_eq ψ t', hψ] at h1
  have hle : Hconj c0 Q ≤ S ⊓ Subgroup.centralizer ({c0⁻¹ * u' * c0} : Set G) := by
    intro a ha
    have ha' : c0 * a * c0⁻¹ ∈ Q := ha
    refine Subgroup.mem_inf.2 ⟨(hmemS a).2 (hQS' ha'), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : c0 * a * c0⁻¹ ∈ Subgroup.centralizer ({u'} : Set G) := hQ.1 ha'
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have : c0 * (a * (c0⁻¹ * u' * c0)) * c0⁻¹ = c0 * ((c0⁻¹ * u' * c0) * a) * c0⁻¹ := by
      calc c0 * (a * (c0⁻¹ * u' * c0)) * c0⁻¹ = (c0 * a * c0⁻¹) * u' := by group
        _ = u' * (c0 * a * c0⁻¹) := hc
        _ = c0 * ((c0⁻¹ * u' * c0) * a) * c0⁻¹ := by group
    simpa using this
  have h2 : Nat.card Q ≤ Nat.card P := by
    calc Nat.card Q = Nat.card (Hconj c0 Q) := (Hconj_card c0 Q).symm
      _ ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({c0⁻¹ * u' * c0} : Set G)) :=
          Subgroup.card_le_of_le hle
      _ ≤ Nat.card P := h1
  have hPQeq : P = Q := Subgroup.eq_of_le_of_card_ge hPQ h2
  have hfin : IsSylow2In P (Subgroup.centralizer ({u'} : Set G)) := by
    rw [hPQeq]
    exact hQ
  exact hfin

end Sylow

section Bridges

variable [Finite G]

theorem card_le_of_extremal (hSp : IsPGroup 2 ↥S) {y : G} (hy : IsExtremal S y) (c : G) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({c * y * c⁻¹} : Set G)) ≤
      Nat.card ↥(S ⊓ Subgroup.centralizer ({y} : Set G)) :=
  card_le_sylow_of_conj (hSp.to_le inf_le_left) inf_le_right hy

theorem card_cent_le_of_extremal (hSp : IsPGroup 2 ↥S) (ψ : ↥S ≃* M) {t' : M}
    (hy : IsExtremal S ((ψ.symm t' : ↥S) : G)) {t'' : M} (h : Erel ψ t' t'') :
    Nat.card ↥(Subgroup.centralizer ({t''} : Set M)) ≤
      Nat.card ↥(Subgroup.centralizer ({t'} : Set M)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [card_cent_eq ψ t'', card_cent_eq ψ t', ← hc]
  exact card_le_of_extremal hSp hy c

theorem card_cent_le_of_conj (hSp : IsPGroup 2 ↥S) (ψ : ↥S ≃* M) {x : G} {T : Subgroup G}
    (hT : IsSylow2In T (Subgroup.centralizer ({x} : Set G))) {t' : M}
    (h : IsConj x ((ψ.symm t' : ↥S) : G)) :
    Nat.card ↥(Subgroup.centralizer ({t'} : Set M)) ≤ Nat.card T := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [card_cent_eq ψ t', ← hc]
  exact card_le_sylow_of_conj (hSp.to_le inf_le_left) inf_le_right hT

theorem scp_bridge (hS : IsSylow2In S ⊤) (ψ : ↥S ≃* M) {t t' : M} (hE : Erel ψ t t')
    (hext : ∀ t'' : M, Erel ψ t' t'' →
      Nat.card ↥(Subgroup.centralizer ({t''} : Set M)) ≤
        Nat.card ↥(Subgroup.centralizer ({t'} : Set M))) :
    ∃ φ : ↥(Subgroup.centralizer ({t} : Set M)) →* ↥(Subgroup.centralizer ({t'} : Set M)),
      Function.Injective φ ∧
      (φ ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : M) = t' ∧
      ∀ s, Erel ψ (φ s : M) (s : M) := by
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 hE
  have hex : IsExtremal S ((ψ.symm t' : ↥S) : G) := isExtremal_of_max hS ψ hext
  obtain ⟨g, hg1, hg2⟩ := scp hS.2.1 hex hg₀
  have hz : ∀ s : ↥(Subgroup.centralizer ({t} : Set M)),
      g * ((ψ.symm s.1 : ↥S) : G) * g⁻¹ ∈
        S ⊓ Subgroup.centralizer ({((ψ.symm t' : ↥S) : G)} : Set G) := fun s =>
    hg2 _ (ψ.symm s.1).2
      (Subgroup.mem_centralizer_singleton_iff.1 ((mem_cent_iff ψ).1 s.2))
  let f : ↥(Subgroup.centralizer ({t} : Set M)) → M := fun s =>
    ψ ⟨g * ((ψ.symm s.1 : ↥S) : G) * g⁻¹, (Subgroup.mem_inf.1 (hz s)).1⟩
  have hfs : ∀ s, ((ψ.symm (f s) : ↥S) : G) = g * ((ψ.symm s.1 : ↥S) : G) * g⁻¹ := fun s => by
    simp [f]
  have hfc : ∀ s, f s ∈ Subgroup.centralizer ({t'} : Set M) := fun s => by
    rw [mem_cent_iff ψ, hfs]
    exact (Subgroup.mem_inf.1 (hz s)).2
  have hmul : ∀ a b : ↥(Subgroup.centralizer ({t} : Set M)), f (a * b) = f a * f b := by
    intro a b
    apply ψ.symm.injective
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, hfs, hfs, hfs]
    simp only [Subgroup.coe_mul, map_mul]
    group
  let φ : ↥(Subgroup.centralizer ({t} : Set M)) →* ↥(Subgroup.centralizer ({t'} : Set M)) :=
    MonoidHom.mk' (fun s => ⟨f s, hfc s⟩) (fun a b => Subtype.ext (hmul a b))
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : f a = f b := congrArg Subtype.val hab
    have h2 := congrArg (fun m => ((ψ.symm m : ↥S) : G)) h1
    simp only [hfs] at h2
    have h3 : ((ψ.symm a.1 : ↥S) : G) = ((ψ.symm b.1 : ↥S) : G) := by
      have := mul_left_cancel (mul_right_cancel h2)
      exact this
    exact Subtype.ext (ψ.symm.injective (Subtype.ext h3))
  · show f ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = t'
    apply ψ.symm.injective
    apply Subtype.ext
    rw [hfs]
    exact hg1
  · intro s
    show IsConj ((ψ.symm (f s) : ↥S) : G) ((ψ.symm s.1 : ↥S) : G)
    rw [hfs, isConj_iff]
    exact ⟨g⁻¹, by simp [mul_assoc]⟩

theorem thompson_bridge (hIG : IG_15_15) (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hS : IsSylow2In S ⊤) (ψ : ↥S ≃* M)
    {H : Subgroup M} (hH : H.index = 2) {u : M} (hu : u ∉ H) (hu2 : u * u = 1) :
    ∃ u' ∈ H, Erel ψ u' u ∧ ∀ u'' : M, Erel ψ u' u'' →
      Nat.card ↥(Subgroup.centralizer ({u''} : Set M)) ≤
        Nat.card ↥(Subgroup.centralizer ({u'} : Set M)) := by
  have hSp : IsPGroup 2 ↥S := hS.2.1
  have : H.Normal := Subgroup.normal_of_index_eq_two hH
  set N : Subgroup G := (H.comap ψ.toMonoidHom).map S.subtype with hN
  have hmemN : ∀ y : G, ∀ hy : y ∈ S, y ∈ N ↔ ψ ⟨y, hy⟩ ∈ H := by
    intro y hy
    rw [hN, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hyH
      exact ⟨⟨y, hy⟩, hyH, rfl⟩
  have hNS : N ≤ S := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := Subgroup.mem_map.1 hy
    exact z.2
  have hmulN : ∀ y z : G, y ∈ S → z ∈ S → (y * z ∈ N ↔ (y ∈ N ↔ z ∈ N)) := by
    intro y z hy hz
    rw [hmemN _ (S.mul_mem hy hz), hmemN _ hy, hmemN _ hz]
    have : ψ ⟨y * z, S.mul_mem hy hz⟩ = ψ ⟨y, hy⟩ * ψ ⟨z, hz⟩ := by
      rw [← map_mul]
      rfl
    rw [this]
    exact Subgroup.mul_mem_iff_of_index_two hH
  have hinvN : ∀ y : G, y ∈ S → (y⁻¹ ∈ N ↔ y ∈ N) := by
    intro y hy
    rw [hmemN _ (S.inv_mem hy), hmemN _ hy]
    have : ψ ⟨y⁻¹, S.inv_mem hy⟩ = (ψ ⟨y, hy⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this]
    exact inv_mem_iff
  set u₀ : G := ((ψ.symm u : ↥S) : G) with hu₀
  have hu₀S : u₀ ∈ S := (ψ.symm u).2
  have hu₀N : u₀ ∉ N := by
    rw [hmemN _ hu₀S]
    have : (⟨u₀, hu₀S⟩ : ↥S) = ψ.symm u := Subtype.coe_eta _ _
    rw [this, MulEquiv.apply_symm_apply]
    exact hu
  have hu₀sq : u₀ * u₀ = 1 := by
    have : ψ.symm (u * u) = 1 := by rw [hu2, map_one]
    rw [map_mul] at this
    exact congrArg Subtype.val this
  have hnorm : ∀ t ∈ S, ∀ q ∈ N, t * q * t⁻¹ ∈ N := by
    intro t ht q hq
    have hqS : q ∈ S := hNS hq
    have hS3 : t * q * t⁻¹ ∈ S := S.mul_mem (S.mul_mem ht hqS) (S.inv_mem ht)
    rw [hmemN _ hS3]
    have hq' := (hmemN _ hqS).1 hq
    have : ψ ⟨t * q * t⁻¹, hS3⟩ = ψ ⟨t, ht⟩ * ψ ⟨q, hqS⟩ * (ψ ⟨t, ht⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact Subgroup.Normal.conj_mem inferInstance _ hq' _
  have hne : N ≠ S := fun hNe => hu₀N (hNe ▸ hu₀S)
  have hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ N := by
    refine ⟨u₀, hu₀S, fun t ht => ?_⟩
    by_cases htN : t ∈ N
    · exact ⟨0, by simpa using htN⟩
    · refine ⟨1, ?_⟩
      rw [zpow_one, hmulN _ _ (S.inv_mem hu₀S) ht]
      exact iff_of_false (fun h => hu₀N ((hinvN _ hu₀S).1 h)) htN
  have hord : ∀ v ∈ S, v ∉ N → orderOf u₀ ≤ orderOf v := by
    intro v hv hvN
    have h1 : orderOf u₀ ≤ 2 :=
      orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hu₀sq)
    have hv1 : v ≠ 1 := fun h => hvN (h ▸ N.one_mem)
    have h2 : orderOf v ≠ 1 := fun h => hv1 (orderOf_eq_one_iff.1 h)
    have h3 : 0 < orderOf v := orderOf_pos v
    omega
  have hext : ∀ y ∈ S, (∃ g : G, g⁻¹ * u₀ * g = y) → IsExtremal S y →
      y ∈ N ∨ u₀⁻¹ * y ∈ N := by
    intro y hy _ _
    by_cases hyN : y ∈ N
    · exact Or.inl hyN
    · right
      rw [hmulN _ _ (S.inv_mem hu₀S) hy]
      exact iff_of_false (fun h => hu₀N ((hinvN _ hu₀S).1 h)) hyN
  obtain ⟨g, hgN, hgext⟩ :=
    transfer_conj hIG hsimple hnab hS hNS hnorm hne hcyc hu₀S hu₀N hord hext
  set y : G := g⁻¹ * u₀ * g with hy
  have hyS : y ∈ S := hNS hgN
  have hsy : ((ψ.symm (ψ ⟨y, hyS⟩) : ↥S) : G) = y := by simp
  refine ⟨ψ ⟨y, hyS⟩, (hmemN _ hyS).1 hgN, ?_, ?_⟩
  · show IsConj ((ψ.symm (ψ ⟨y, hyS⟩) : ↥S) : G) ((ψ.symm u : ↥S) : G)
    rw [hsy, isConj_iff]
    exact ⟨g, by
      calc g * y * g⁻¹ = u₀ := by rw [hy]; group
        _ = _ := hu₀⟩
  · intro u'' hu''
    exact card_cent_le_of_extremal hSp ψ (by rw [hsy]; exact hgext) hu''


end Bridges

end CFSG.GH74.GLS.C3.Layer2.L5
