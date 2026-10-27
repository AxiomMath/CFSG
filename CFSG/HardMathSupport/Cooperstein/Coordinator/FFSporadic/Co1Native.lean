module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Cut
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1F0
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Disp
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Local
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1RankSylow
public import CFSG.Sporadic.Co1Patterson.NativeSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Co1Patterson CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier
  CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial

section Transport

noncomputable def cNC : NativeSporadic.Co1 := co1MatEquiv.symm cC

noncomputable def bNC : NativeSporadic.Co1 := co1MatEquiv.symm a₁

theorem co1MatEquiv_cNC : co1MatEquiv cNC = cC := MulEquiv.apply_symm_apply _ _

theorem co1MatEquiv_bNC : co1MatEquiv bNC = a₁ := MulEquiv.apply_symm_apply _ _

theorem nativeEmb_cNC : nativeEmb cNC = (iotaC : GL24) :=
  (nativeEmb_apply cNC).trans ((congrArg (fun x : GA => (x : GL24)) co1MatEquiv_cNC).trans coe_cC)

theorem nativeEmb_bNC : nativeEmb bNC = A₁ :=
  (nativeEmb_apply bNC).trans ((congrArg (fun x : GA => (x : GL24)) co1MatEquiv_bNC).trans coe_a₁)

theorem co1MatEquiv_aNC' : co1MatEquiv aNC = aC := co1MatEquiv_aNC

theorem Y_classes :
    ∀ y : NativeSporadic.Co1, orderOf y = 2 → IsConj y aNC ∨ IsConj y cNC ∨ IsConj y bNC := by
  intro y hy
  have hy' : orderOf (co1MatEquiv y) = 2 := by rw [orderOf_co1MatEquiv, hy]
  have key : ∀ r : NativeSporadic.Co1, IsConj (co1MatEquiv y) (co1MatEquiv r) → IsConj y r := by
    intro r h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨co1MatEquiv.symm c, co1MatEquiv.injective ?_⟩
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply, hc]
  rcases involution_classes.1 _ hy' with h | h | h
  · exact Or.inl (key _ (by rw [co1MatEquiv_aNC']; exact h))
  · exact Or.inr (Or.inl (key _ (by rw [co1MatEquiv_cNC]; exact h)))
  · exact Or.inr (Or.inr (key _ (by rw [co1MatEquiv_bNC]; exact h)))

theorem isConj_co1 {a b : NativeSporadic.Co1} (h : IsConj a b) :
    IsConj (co1MatEquiv a) (co1MatEquiv b) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨co1MatEquiv c, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hc]

theorem aNC_sq :
    aNC * aNC = 1 := by
  have := pow_orderOf_eq_one aNC
  rwa [orderOf_aNC, sq] at this

theorem ncard_xFix_ne_of_not_A
    {y : NativeSporadic.Co1} (hy : orderOf y = 2) (hyA : y ∉ classOf aNC) :
    (xFix (nativeEmb y)).ncard ≠ 2280 := by
  rcases Y_classes y hy with h | h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact absurd ⟨c⁻¹, by rw [← hc]; group⟩ hyA
  · have h1 : IsConj (co1MatEquiv y) cC := by
      have := isConj_co1 h
      rwa [co1MatEquiv_cNC] at this
    have h' := ncard_fix_isConj h1
    rw [ncard_fix_cC] at h'
    rw [nativeEmb_apply, ← h']
    norm_num
  · have h1 : IsConj (co1MatEquiv y) a₁ := by
      have := isConj_co1 h
      rwa [co1MatEquiv_bNC] at this
    have h' := ncard_fix_isConj h1
    rw [ncard_fix_a₁] at h'
    rw [nativeEmb_apply, ← h']
    norm_num

theorem mem_cent_Y {w x : NativeSporadic.Co1} :
    x ∈ Subgroup.centralizer ({w} : Set NativeSporadic.Co1) ↔ x * w = w * x :=
  @Subgroup.mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance w x

theorem gen_transport {u v : NativeSporadic.Co1}
    (h : (GA ⊓ Subgroup.centralizer ({nativeEmb u} : Set GL24)) ⊔
      (GA ⊓ Subgroup.centralizer ({nativeEmb v} : Set GL24)) = GA) :
    Subgroup.centralizer ({u} : Set NativeSporadic.Co1) ⊔
        Subgroup.centralizer ({v} : Set NativeSporadic.Co1) = ⊤ := by
  have hmap : ∀ w : NativeSporadic.Co1, (Subgroup.centralizer ({w} : Set NativeSporadic.Co1)).map
      nativeEmb = GA ⊓ Subgroup.centralizer ({nativeEmb w} : Set GL24) := by
    intro w
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_inf.2 ⟨nativeEmb_mem x, ?_⟩
      have h1 : x * w = w * x := mem_cent_Y.1 hx
      exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, h1])
    · intro hg
      obtain ⟨hgA, hgC⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨x, rfl⟩ := exists_nativeEmb_eq hgA
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 hgC
      have h3 : nativeEmb (x * w) = nativeEmb (w * x) := by rw [map_mul, map_mul]; exact h2
      exact ⟨x, mem_cent_Y.2 (nativeEmb_injective h3), rfl⟩
  have hsup : (Subgroup.centralizer ({u} : Set NativeSporadic.Co1) ⊔
      Subgroup.centralizer ({v} : Set NativeSporadic.Co1)).map nativeEmb = GA := by
    rw [Subgroup.map_sup, hmap, hmap]
    exact h
  rw [eq_top_iff]
  intro y _
  have hy : nativeEmb y ∈ (Subgroup.centralizer ({u} : Set NativeSporadic.Co1) ⊔
      Subgroup.centralizer ({v} : Set NativeSporadic.Co1)).map nativeEmb := by
    rw [hsup]
    exact nativeEmb_mem y
  obtain ⟨w, hw, hwy⟩ := hy
  rwa [← nativeEmb_injective hwy]

theorem dih_of_conj {G : Type*} [Group G] {r t g : G} (hr : ∃ c₁ : G, orderOf (r * (c₁ * r * c₁⁻¹)) = 13)
    (h : g * t * g⁻¹ = r) : ∃ c : G, orderOf (t * (c * t * c⁻¹)) = 13 := by
  obtain ⟨c₁, hc₁⟩ := hr
  refine ⟨g⁻¹ * c₁ * g, ?_⟩
  have ht : t = g⁻¹ * r * g := by rw [← h]; group
  have e : t * (g⁻¹ * c₁ * g * t * (g⁻¹ * c₁ * g)⁻¹) = g⁻¹ * (r * (c₁ * r * c₁⁻¹)) * g := by
    rw [ht]; group
  rw [e]
  have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (r * (c₁ * r * c₁⁻¹))
  rw [MulAut.conj_apply, inv_inv] at this
  rw [this, hc₁]

theorem emb_mul_eq {x y z : NativeSporadic.Co1}
    (h : nativeEmb x * nativeEmb y = nativeEmb z) : x * y = z := by
  rw [← map_mul] at h
  exact nativeEmb_injective h

theorem emb_conj_eq {s a b : NativeSporadic.Co1}
    (h : nativeEmb s * nativeEmb a * (nativeEmb s)⁻¹ = nativeEmb b) : s * a * s⁻¹ = b := by
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact nativeEmb_injective h

theorem emb_ne {x y : NativeSporadic.Co1}
    (h : nativeEmb x ≠ nativeEmb y) : x ≠ y := fun e => h (congrArg nativeEmb e)

theorem emb_pow {x : NativeSporadic.Co1} {n : ℕ}
    (h : nativeEmb x ^ n = 1) : x ^ n = 1 := by
  rw [← map_pow, ← map_one nativeEmb] at h
  exact nativeEmb_injective h

theorem emb_comm_eq {x y : NativeSporadic.Co1}
    (h : nativeEmb x * nativeEmb y = nativeEmb y * nativeEmb x) : x * y = y * x := by
  rw [← map_mul, ← map_mul] at h
  exact nativeEmb_injective h

theorem Q_data :
    ∃ Q : NativeSporadic.Co1 → Subgroup NativeSporadic.Co1,
      (∀ z ∈ classOf aNC, ∀ N : Subgroup NativeSporadic.Co1,
        N ≤ Subgroup.centralizer ({z} : Set NativeSporadic.Co1) →
        (∀ c ∈ Subgroup.centralizer ({z} : Set NativeSporadic.Co1), ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
          N ≤ Q z ∨ N = Subgroup.centralizer ({z} : Set NativeSporadic.Co1)) ∧
      (∀ z ∈ classOf aNC, ∀ B : Subgroup NativeSporadic.Co1, B ≤ Q z →
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 5) := by
  have hw := width_nativeSetting
  have hΩ := map_Mbar_eq_omega_of_card nativeSetting hw card_Mbar_nativeSetting
  have h8 := finrank_Qt_of_width_four nativeSetting hw
  refine exists_Q_of_base aNC nativeSetting.QG ?_ ?_
  · intro N hN hnorm
    exact le_QG_or_eq_M nativeSetting hΩ h8 hN hnorm
  · intro B hB hcomm _
    have := nativeSetting.card_le_of_commute hB hcomm
    rwa [hw] at this

theorem f0_Y :
    ∃ b s₁ s₂ : NativeSporadic.Co1, b * b = 1 ∧ b ≠ 1 ∧ b ≠ aNC ∧ aNC * b = b * aNC ∧
      s₁ * aNC * s₁⁻¹ = b ∧ s₁ * b * s₁⁻¹ = aNC ∧ s₂ * b * s₂⁻¹ = aNC * b ∧
      s₂ * (aNC * b) * s₂⁻¹ = b ∧
      Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1) ⊔
        Subgroup.centralizer ({b} : Set NativeSporadic.Co1) = ⊤ := by
  obtain ⟨b₀, t₁, t₂, hb, ht₁, ht₂, hbb, hb1, hba, hab, hs1a, hs1b, hs2b, hs2ab, hgen⟩ := f0_facts
  obtain ⟨b, hbe⟩ := exists_nativeEmb_eq hb
  obtain ⟨s₁, hs₁⟩ := exists_nativeEmb_eq ht₁
  obtain ⟨s₂, hs₂⟩ := exists_nativeEmb_eq ht₂
  have ha : nativeEmb aNC = (iotaA : GL24) := nativeEmb_aNC
  refine ⟨b, s₁, s₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine emb_mul_eq ?_
    rw [hbe, map_one]
    exact hbb
  · exact emb_ne (by rw [hbe, map_one]; exact hb1)
  · exact emb_ne (by rw [hbe, ha]; exact hba)
  · refine emb_comm_eq ?_
    rw [ha, hbe]
    exact hab
  · refine emb_conj_eq ?_
    rw [hs₁, ha, hbe]
    exact hs1a
  · refine emb_conj_eq ?_
    rw [hs₁, ha, hbe]
    exact hs1b
  · refine emb_conj_eq ?_
    rw [map_mul, hs₂, ha, hbe]
    exact hs2b
  · refine emb_conj_eq ?_
    rw [map_mul, hs₂, ha, hbe]
    exact hs2ab
  · refine gen_transport ?_
    rw [ha, hbe]
    exact hgen

theorem heis_yx {G : Type*} [Group G] (x y : G) : y⁻¹ * x * y = x * (x⁻¹ * y⁻¹ * x * y) := by
  group

theorem heis_Y :
    ∃ x y : NativeSporadic.Co1, CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisCfg 5 (0 + 1)
      (fun _ => x) (fun _ => y) (x⁻¹ * y⁻¹ * x * y) ∧ aNC * x * aNC⁻¹ = x⁻¹ := by
  obtain ⟨X, Y', hX, hY, hX5, hY5, hW5, hW1, hXW, hYW, haX⟩ := heis_facts
  obtain ⟨x, hxe⟩ := exists_nativeEmb_eq hX
  obtain ⟨y, hye⟩ := exists_nativeEmb_eq hY
  have hz : nativeEmb (x⁻¹ * y⁻¹ * x * y) = X⁻¹ * Y'⁻¹ * X * Y' := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxe, hye]
  have hxp : x ^ 5 = 1 := emb_pow (by rw [hxe]; exact hX5)
  have hzp : (x⁻¹ * y⁻¹ * x * y) ^ 5 = 1 := emb_pow (by rw [hz]; exact hW5)
  have hzx : x * (x⁻¹ * y⁻¹ * x * y) = (x⁻¹ * y⁻¹ * x * y) * x :=
    emb_comm_eq (by rw [hz, hxe]; exact hXW)
  have hzy : y * (x⁻¹ * y⁻¹ * x * y) = (x⁻¹ * y⁻¹ * x * y) * y :=
    emb_comm_eq (by rw [hz, hye]; exact hYW)
  have hz1 : x⁻¹ * y⁻¹ * x * y ≠ 1 := emb_ne (by rw [hz, map_one]; exact hW1)
  refine ⟨x, y, ?_, ?_⟩
  · exact
    { xp := fun _ => hxp
      zp := hzp
      zx := fun _ => hzx
      zy := fun _ => hzy
      yx := fun _ => heis_yx x y
      xx := fun _ _ => rfl
      yy := fun i j hij => absurd (Fin.eq_of_val_eq (by have := i.2; have := j.2; omega)) hij
      xy := fun i j hij => absurd (Fin.eq_of_val_eq (by have := i.2; have := j.2; omega)) hij
      z1 := hz1 }
  · refine emb_conj_eq ?_
    rw [map_inv, hxe, nativeEmb_aNC]
    exact haX

theorem dih_Y :
    (∃ c : NativeSporadic.Co1, orderOf (cNC * (c * cNC * c⁻¹)) = 13) ∧
      (∃ c : NativeSporadic.Co1, orderOf (bNC * (c * bNC * c⁻¹)) = 13) := by
  obtain ⟨⟨cc, hcc, hcc13⟩, ⟨ca, hca, hca13⟩⟩ := dih_facts
  obtain ⟨c₁, hc₁⟩ := exists_nativeEmb_eq hcc
  obtain ⟨c₂, hc₂⟩ := exists_nativeEmb_eq hca
  refine ⟨⟨c₁, ?_⟩, ⟨c₂, ?_⟩⟩
  · rw [← orderOf_injective nativeEmb nativeEmb_injective]
    rw [map_mul, map_mul, map_mul, map_inv, nativeEmb_cNC, hc₁]
    exact hcc13
  · rw [← orderOf_injective nativeEmb nativeEmb_injective]
    rw [map_mul, map_mul, map_mul, map_inv, nativeEmb_bNC, hc₂]
    exact hca13

section Generic

variable {G : Type} [Group G]

theorem sq_conj_self {a : G} (g : G) (h : a * a = 1) : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
  calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem ne_one_conj {a : G} (g : G) (h : a ≠ 1) : g * a * g⁻¹ ≠ 1 := by
  intro h1
  apply h
  calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

theorem conj_of_conj {a z z' g₁ g₂ : G} (h : z = g₁ * a * g₁⁻¹) (h' : z' = g₂ * a * g₂⁻¹) :
    z' = (g₂ * g₁⁻¹) * z * (g₂ * g₁⁻¹)⁻¹ := by
  rw [h, h']
  group

theorem conj_comp {a b c s₁ s₂ : G} (h₁ : s₁ * a * s₁⁻¹ = b) (h₂ : s₂ * b * s₂⁻¹ = c) :
    c = (s₂ * s₁) * a * (s₂ * s₁)⁻¹ := by
  rw [← h₂, ← h₁]
  group

theorem conj_fix_a {a b s : G} (haa : a * a = 1) (h₁ : s * (a * b) * s⁻¹ = b)
    (h₂ : s * b * s⁻¹ = a * b) : s * a * s⁻¹ = a := by
  have e : s * a * s⁻¹ = (s * (a * b) * s⁻¹) * (s * b * s⁻¹)⁻¹ := by group
  rw [e, h₁, h₂]
  have : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  calc b * (a * b)⁻¹ = a⁻¹ := by group
    _ = a := this

theorem conj_fix_ab {a b s : G} (hc : a * b = b * a) (h₁ : s * a * s⁻¹ = b)
    (h₂ : s * b * s⁻¹ = a) : s * (a * b) * s⁻¹ = a * b := by
  have e : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
  rw [e, h₁, h₂, hc]

theorem heis_conj (g x y : G)
    (h : CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisCfg 5 (0 + 1)
      (fun _ => x) (fun _ => y) (x⁻¹ * y⁻¹ * x * y)) :
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisCfg 5 (0 + 1)
      (fun _ => g * x * g⁻¹) (fun _ => g * y * g⁻¹) (g * (x⁻¹ * y⁻¹ * x * y) * g⁻¹) := by
  have hfz : (MulAut.conj g).toMonoidHom (x⁻¹ * y⁻¹ * x * y) ≠ 1 := fun h1 =>
    h.z1 ((MulAut.conj g).injective (by simpa using h1))
  exact CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisCfg.map (MulAut.conj g).toMonoidHom h hfz

theorem inv_conj_conj (g a x : G) (h : a * x * a⁻¹ = x⁻¹) :
    (g * a * g⁻¹) * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹ = (g * x * g⁻¹)⁻¹ := by
  calc (g * a * g⁻¹) * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹ = g * (a * x * a⁻¹) * g⁻¹ := by group
    _ = g * x⁻¹ * g⁻¹ := by rw [h]
    _ = (g * x * g⁻¹)⁻¹ := by group

theorem one_conj (a : G) : a = 1 * a * 1⁻¹ := by group

theorem mem_class_of_conj {a t g : G} (h : g * t * g⁻¹ = a) :
    t ∈ classOf a := ⟨g⁻¹, by rw [← h]; group⟩

end Generic

theorem cutData_Co1 :
    Nonempty (CutData NativeSporadic.Co1) := by
  obtain ⟨Q, hdich, hrank⟩ := Q_data
  obtain ⟨b, s₁, s₂, hbb, hb1, hba, hcab, hs1a, hs1b, hs2b, hs2ab, hgen⟩ := f0_Y
  obtain ⟨x, y, hHeis, hax⟩ := heis_Y
  obtain ⟨hdc, hdb⟩ := dih_Y
  have hasq := aNC_sq
  have ha1 : aNC ≠ 1 := fun h =>
    absurd ((orderOf_eq_one_iff.2 h).symm.trans orderOf_aNC) (by norm_num)
  have h2a : s₂ * aNC * s₂⁻¹ = aNC :=
    @conj_fix_a NativeSporadic.Co1 inferInstance _ _ _ hasq hs2ab hs2b
  have h1ab : s₁ * (aNC * b) * s₁⁻¹ = aNC * b :=
    @conj_fix_ab NativeSporadic.Co1 inferInstance _ _ _ hcab hs1a hs1b
  refine ⟨{ A := classOf aNC
            Q := Q
            a := aNC
            b := b
            A_inv := ?_
            A_conj := ?_
            ha := ?_
            hb := ?_
            hab := ?_
            hab_comm := hcab
            hab_ne := fun h => hba h.symm
            gen₁ := hgen
            gen₂ := ?_
            gen₃ := ?_
            dich := hdich
            Q_rank := hrank
            noA_rank := ?_
            heisA := ?_
            dihNonA := ?_ }⟩
  · rintro z ⟨g, rfl⟩
    exact ⟨@sq_conj_self NativeSporadic.Co1 inferInstance aNC g hasq,
      @ne_one_conj NativeSporadic.Co1 inferInstance aNC g ha1⟩
  · rintro z ⟨g₁, hz⟩ z' ⟨g₂, hz'⟩
    exact ⟨g₂ * g₁⁻¹, @conj_of_conj NativeSporadic.Co1 inferInstance aNC z z' g₁ g₂ hz hz'⟩
  · exact ⟨1, @one_conj NativeSporadic.Co1 inferInstance aNC⟩
  · exact ⟨s₁, hs1a.symm⟩
  · exact ⟨s₂ * s₁, @conj_comp NativeSporadic.Co1 inferInstance aNC b (aNC * b) s₁ s₂ hs1a hs2b⟩
  · have := @gen_conj NativeSporadic.Co1 inferInstance aNC b hgen s₂
    rwa [h2a, hs2b] at this
  · have h2 : Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1) ⊔
        Subgroup.centralizer ({aNC * b} : Set NativeSporadic.Co1) = ⊤ := by
      have := @gen_conj NativeSporadic.Co1 inferInstance aNC b hgen s₂
      rwa [h2a, hs2b] at this
    have := @gen_conj NativeSporadic.Co1 inferInstance aNC (aNC * b) h2 s₁
    rwa [hs1a, h1ab] at this
  · intro B hcomm hsq hnA
    have hBGA : B.map nativeEmb ≤ GA := by
      rintro _ ⟨x, -, rfl⟩
      exact nativeEmb_mem x
    have hcomm' : ∀ u ∈ B.map nativeEmb, ∀ v ∈ B.map nativeEmb, u * v = v * u := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy]
    have hsq' : ∀ u ∈ B.map nativeEmb, u * u = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hsq x hx, map_one]
    have hnA' : ∀ u ∈ B.map nativeEmb, u ≠ 1 → (xFix u).ncard ≠ 2280 := by
      rintro _ ⟨x, hx, rfl⟩ hx1
      have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
      have ho : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hsq x hx) hx1'
      exact ncard_xFix_ne_of_not_A ho (hnA x hx hx1')
    have := noA_rank_GA hBGA hcomm' hsq' hnA'
    rwa [Subgroup.card_map_of_injective nativeEmb_injective] at this
  · rintro t ⟨g, rfl⟩
    exact ⟨fun _ => g * x * g⁻¹, fun _ => g * y * g⁻¹, g * (x⁻¹ * y⁻¹ * x * y) * g⁻¹,
      @heis_conj NativeSporadic.Co1 inferInstance g x y hHeis,
      @inv_conj_conj NativeSporadic.Co1 inferInstance g aNC x hax⟩
  · intro t hsq ht1 htA
    have ho : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact hsq) ht1
    rcases Y_classes t ho with h | h | h
    · obtain ⟨g, hg⟩ := isConj_iff.1 h
      exact absurd (@mem_class_of_conj NativeSporadic.Co1 inferInstance aNC t g hg) htA
    · obtain ⟨g, hg⟩ := isConj_iff.1 h
      exact @dih_of_conj NativeSporadic.Co1 inferInstance cNC t g hdc hg
    · obtain ⟨g, hg⟩ := isConj_iff.1 h
      exact @dih_of_conj NativeSporadic.Co1 inferInstance bNC t g hdb hg

end Transport

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
