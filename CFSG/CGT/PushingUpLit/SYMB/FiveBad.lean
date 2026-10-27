module

public import CFSG.CGT.PushingUpLit.SYMB.FiveCoho
public import CFSG.CGT.PushingUpLit.SYMB.Delta5Fix
public import CFSG.CGT.PushingUpLit.SYMB.FiveStruct

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {V₁ E : Subgroup Γ}

namespace V1Iso

omit [Finite Γ] in
theorem centralizer_E_trivial (hV : V1Iso S V₁) (h : FiveCase S E) {v : Γ} (hv : v ∈ V₁)
    (hc : ∀ e ∈ E, e * v * e⁻¹ = v) : v = 1 := by
  have h1 : ψ ⟨v, hV.le hv⟩ = 1 := by
    apply Delta5Fix.no_fixed
    intro σ hσ
    have hσA : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hσ
    have hσE : σ ∈ imgG G φ E := by
      rw [h.join.img_eq_alt]
      exact hσA
    obtain ⟨e, heG, heE, hφe⟩ := mem_imgG.1 hσE
    have := hV.psi_conj heG hv
    rw [hφe] at this
    rw [← this]
    congr 1
    apply Subtype.ext
    exact hc e heE
  have h2 : (⟨v, hV.le hv⟩ : ↥V) = 1 := hV.inj _ hv h1
  exact congrArg Subtype.val h2

omit [Finite Γ] in
theorem comm_V₁_E (hV : V1Iso S V₁) (h : FiveCase S E) : ⁅V₁, E⁆ = V₁ := by
  classical
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv e he
    have e1 : ⁅v, e⁆ = v * (e * v⁻¹ * e⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e1]
    exact V₁.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hV.normal (h.join.le he)) v⁻¹).mp
      (V₁.inv_mem hv))
  · set X : Subgroup Γ := ⁅V₁, E⁆ with hX
    have hXV₁ : X ≤ V₁ := by
      rw [Subgroup.commutator_le]
      intro v hv e he
      have e1 : ⁅v, e⁆ = v * (e * v⁻¹ * e⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [e1]
      exact V₁.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hV.normal (h.join.le he)) v⁻¹).mp
        (V₁.inv_mem hv))
    let Z : Subgroup ↥(G6.coreMod 5) := (X.subgroupOf V).map ψ
    have hZ : ∀ w, w ∈ Z := by
      intro w
      have hcl := Delta5Fix.comm_closure w
      refine (Subgroup.closure_le Z).2 ?_ hcl
      rintro x ⟨σ, u, hσ, rfl⟩
      have hσA : σ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 hσ
      have hσE : σ ∈ imgG G φ E := by
        rw [h.join.img_eq_alt]
        exact hσA
      obtain ⟨e, heG, heE, hφe⟩ := mem_imgG.1 hσE
      obtain ⟨v, hvV₁, hψv⟩ := hV.surj u
      have hconj : e * (v : Γ) * e⁻¹ ∈ V₁ :=
        (Subgroup.mem_normalizer_iff.mp (hV.normal heG) _).mp hvV₁
      have hcomm : ⁅(v : Γ), e⁆ ∈ X := Subgroup.commutator_mem_commutator hvV₁ heE
      have hinv : ⁅e, (v : Γ)⁆ ∈ X := by
        have := X.inv_mem hcomm
        rwa [commutatorElement_inv] at this
      have hmemV : ⁅e, (v : Γ)⁆ ∈ V := hV.le (hXV₁ hinv)
      refine ⟨⟨_, hmemV⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 hinv
      · have h3 : ψ ⟨⁅e, (v : Γ)⁆, hmemV⟩ = ψ ⟨e * (v : Γ) * e⁻¹, hV.le hconj⟩ * (ψ v)⁻¹ := by
          have h4 := map_mul ψ (⟨e * (v : Γ) * e⁻¹, hV.le hconj⟩ : ↥V) v⁻¹
          rw [map_inv] at h4
          exact h4
        rw [h3, hV.psi_conj heG hvV₁, hφe, hψv]
    intro v hv
    obtain ⟨x, hx, hψx⟩ := hZ (ψ ⟨v, hV.le hv⟩)
    have hxX : (x : Γ) ∈ X := Subgroup.mem_subgroupOf.1 hx
    have := hV.eq_of_psi_eq (hXV₁ hxX) hv (by
      have e1 : (⟨(x : ↥V), x.2⟩ : ↥V) = x := rfl
      simpa using hψx)
    rw [← this]
    exact hxX

end V1Iso

theorem aux_central {M : Type*} [Group M] (y e a b : M) (hc : y * e * y⁻¹ * e⁻¹ = a * b⁻¹)
    (hyb : y * b = b * y) (hae : e * b * e⁻¹ = a) (hab : a * b = b * a) (ha2 : a * a = 1)
    (hb2 : b * b = 1) : (y * b⁻¹) * e = e * (y * b⁻¹) := by
  have h1 : y * e = (a * b⁻¹) * e * y := by
    calc y * e = (y * e * y⁻¹ * e⁻¹) * e * y := by group
      _ = (a * b⁻¹) * e * y := by rw [hc]
  have hb' : y * b⁻¹ = b⁻¹ * y := by
    calc y * b⁻¹ = b⁻¹ * (b * y) * b⁻¹ := by group
      _ = b⁻¹ * (y * b) * b⁻¹ := by rw [hyb]
      _ = b⁻¹ * y := by group
  have h2 : e * b⁻¹ = a⁻¹ * e := by
    have : e * b⁻¹ * e⁻¹ = a⁻¹ := by
      rw [← hae]
      group
    calc e * b⁻¹ = (e * b⁻¹ * e⁻¹) * e := by group
      _ = a⁻¹ * e := by rw [this]
  have h3 : b⁻¹ * a * b⁻¹ = a⁻¹ := by
    have hba : b⁻¹ * a = a * b⁻¹ := by
      calc b⁻¹ * a = b⁻¹ * (a * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * a) * b⁻¹ := by rw [hab]
        _ = a * b⁻¹ := by group
    have hbb : b⁻¹ * b⁻¹ = 1 := by
      calc b⁻¹ * b⁻¹ = (b * b)⁻¹ := by group
        _ = 1 := by rw [hb2, inv_one]
    have haa : a⁻¹ = a := by
      calc a⁻¹ = a⁻¹ * (a * a) := by rw [ha2, mul_one]
        _ = a := by group
    calc b⁻¹ * a * b⁻¹ = a * (b⁻¹ * b⁻¹) := by rw [hba]; group
      _ = a⁻¹ := by rw [hbb, mul_one, haa]
  calc (y * b⁻¹) * e = b⁻¹ * (y * e) := by rw [hb']; group
    _ = b⁻¹ * ((a * b⁻¹) * e * y) := by rw [h1]
    _ = (b⁻¹ * a * b⁻¹) * e * y := by group
    _ = a⁻¹ * e * y := by rw [h3]
    _ = e * b⁻¹ * y := by rw [← h2]
    _ = e * (y * b⁻¹) := by rw [hb']; group

theorem exists_central_gen (hV : V1Iso S V₁) (h : FiveCase S E) (hV₁ : V₁ = ⁅V, E⁆) {y : Γ}
    (hy : y ∈ E ⊓ Subgroup.centralizer (V : Set Γ))
    (hKy : E ⊓ Subgroup.centralizer (V : Set Γ) ≤ Subgroup.zpowers y ⊔ V₁) (hy2 : y ^ 2 ∈ V₁)
    (hybad : y ∉ V₁) :
    ∃ z : Γ, z ∈ E ⊓ Subgroup.centralizer (V : Set Γ) ∧ z ∉ V₁ ∧ z ^ 2 = 1 ∧
      (∀ g ∈ G, g * z = z * g) ∧ y⁻¹ * z ∈ V₁ ∧
      ∀ κ ∈ E ⊓ Subgroup.centralizer (V : Set Γ), ∃ v ∈ V₁, κ = v ∨ κ = z * v := by
  classical
  set K : Subgroup Γ := E ⊓ Subgroup.centralizer (V : Set Γ) with hK
  have hEG : E ≤ G := h.join.le
  have hV₁V : V₁ ≤ V := hV.le
  have hV₁comm : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (S.data.elemAbelian.1.is_comm.comm ⟨a, hV₁V ha⟩ ⟨b, hV₁V hb⟩)
  have hV₁sq : ∀ a ∈ V₁, a * a = 1 := fun a ha => by
    have := S.data.elemAbelian.2 a (hV₁V ha)
    rwa [sq] at this
  have hCV : ∀ r ∈ Subgroup.centralizer (V : Set Γ), ∀ v ∈ V₁, v * r = r * v :=
    fun r hr v hv => Subgroup.mem_centralizer_iff.1 hr v (hV₁V hv)
  have hKdec : ∀ κ ∈ K, ∃ j : ℤ, ∃ n ∈ V₁, κ = y ^ j * n := by
    intro κ hκ
    have hmul : ((Subgroup.zpowers y ⊔ V₁ : Subgroup Γ) : Set Γ) =
        (Subgroup.zpowers y : Set Γ) * (V₁ : Set Γ) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (Subgroup.zpowers_le.2 (hV.normal (hEG hy.1)))
    have hκ' : κ ∈ ((Subgroup.zpowers y ⊔ V₁ : Subgroup Γ) : Set Γ) := hKy hκ
    rw [hmul] at hκ'
    obtain ⟨x, hx, n, hn, rfl⟩ := hκ'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ⟨j, n, hn, rfl⟩
  have hycomm : ∀ κ ∈ K, y * κ = κ * y := by
    intro κ hκ
    obtain ⟨j, n, hn, rfl⟩ := hKdec κ hκ
    have h1 : y * (y ^ j) = (y ^ j) * y := (Commute.self_zpow y j).eq
    calc y * (y ^ j * n) = (y * y ^ j) * n := by group
      _ = (y ^ j * y) * n := by rw [h1]
      _ = y ^ j * (y * n) := by group
      _ = y ^ j * (n * y) := by rw [(hCV y hy.2 n hn).symm]
      _ = (y ^ j * n) * y := by group
  have hA : ∀ e (he : e ∈ E), φ ⟨e, hEG he⟩ ∈ alternatingGroup (Fin 5) :=
    fun e he => h.join.map_mem_alt he
  have hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ e, ∃ he : e ∈ E, φ ⟨e, hEG he⟩ = σ := by
    intro σ hσ
    have : σ ∈ imgG G φ E := by
      rw [h.join.img_eq_alt]
      exact hσ
    obtain ⟨e, heG, heE, hφ⟩ := mem_imgG.1 this
    exact ⟨e, heE, hφ⟩
  have hcV : ∀ e ∈ E, ⁅y, e⁆ ∈ V₁ := by
    intro e he
    rw [hV₁]
    exact h.comm_K_E (Subgroup.commutator_mem_commutator hy he)
  obtain ⟨v₁, hv₁, hcv⟩ := crossedHom_principal hV hEG hA hs (fun e => ⁅y, e⁆) hcV
    (fun e _ e' _ => by simp only [commutatorElement_def]; group)
    (fun e he he1 => by
      have heK : e ∈ K := ⟨he, FiveCase.ker_le_centralizer S (mem_kerG.2 ⟨hEG he, he1⟩)⟩
      exact commutatorElement_eq_one_iff_mul_comm.2 (hycomm e heK))
  have hyv : y * v₁ = v₁ * y := (hCV y hy.2 v₁ hv₁).symm
  have hv₁K : v₁ ∈ K := h.V₁_le_K (hV₁ ▸ hv₁)
  obtain ⟨z, hzdef⟩ : ∃ z : Γ, z = y * v₁⁻¹ := ⟨_, rfl⟩
  have hzE : ∀ e ∈ E, z * e = e * z := by
    intro e he
    have hconj : e * v₁ * e⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hV.normal (hEG he)) v₁).mp hv₁
    rw [hzdef]
    refine aux_central y e (e * v₁ * e⁻¹) v₁ ?_ hyv rfl (hV₁comm _ hconj _ hv₁)
      (hV₁sq _ hconj) (hV₁sq _ hv₁)
    exact (commutatorElement_def y e).symm.trans (hcv e he)
  have hyz : y = z * v₁ := by rw [hzdef]; group
  have hzK : z ∈ K := by rw [hzdef]; exact K.mul_mem hy (K.inv_mem hv₁K)
  have hzV₁ : z ∉ V₁ := fun hz => hybad (by rw [hyz]; exact V₁.mul_mem hz hv₁)
  have hzv : z * v₁ = v₁ * z := by
    have := hzE v₁ hv₁K.1
    exact this
  have hyy : y * y ∈ V₁ := by rwa [sq] at hy2
  have hzz : z * z ∈ V₁ := by
    have h1 : y * y = z * z * (v₁ * v₁) := by
      calc y * y = (z * v₁) * (z * v₁) := by rw [← hyz]
        _ = z * (v₁ * z) * v₁ := by group
        _ = z * (z * v₁) * v₁ := by rw [← hzv]
        _ = z * z * (v₁ * v₁) := by group
    rw [hV₁sq v₁ hv₁, mul_one] at h1
    rw [← h1]
    exact hyy
  have hz2 : z ^ 2 = 1 := by
    rw [sq]
    refine hV.centralizer_E_trivial h (v := z * z) hzz ?_
    intro e he
    have hez : e * z * e⁻¹ = z := by rw [← hzE e he]; group
    calc e * (z * z) * e⁻¹ = (e * z * e⁻¹) * (e * z * e⁻¹) := by group
      _ = z * z := by rw [hez]
  have hKshape : ∀ κ ∈ K, ∃ v ∈ V₁, κ = v ∨ κ = z * v := by
    intro κ hκ
    obtain ⟨j, n, hn, rfl⟩ := hKdec κ hκ
    have hcz : Commute z v₁ := hzv
    have hyj : y ^ j = z ^ j * v₁ ^ j := by
      rw [hyz]
      exact hcz.mul_zpow j
    have hzsq : z ^ (2 : ℤ) = 1 := by
      rw [zpow_two, ← sq]
      exact hz2
    have hzj : z ^ j = 1 ∨ z ^ j = z := by
      rcases Int.even_or_odd' j with ⟨k, hk | hk⟩
      · left
        rw [hk, zpow_mul, hzsq, one_zpow]
      · right
        rw [hk, zpow_add, zpow_mul, zpow_one, hzsq, one_zpow, one_mul]
    have hm : v₁ ^ j * n ∈ V₁ := V₁.mul_mem (V₁.zpow_mem hv₁ j) hn
    refine ⟨v₁ ^ j * n, hm, ?_⟩
    rcases hzj with h1 | h1
    · left
      rw [hyj, h1, one_mul]
    · right
      rw [hyj, h1, mul_assoc]
  refine ⟨z, hzK, hzV₁, hz2, ?_, ?_, hKshape⟩
  ·
    intro g hg
    have hgK : g * z * g⁻¹ ∈ K := by
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.mp (h.normal hg) _).mp hzK.1,
        Subgroup.mem_centralizer_iff.2 ?_⟩
      intro w hw
      have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ V := S.data.conj_mem (G.inv_mem hg) hw
      have h1 := Subgroup.mem_centralizer_iff.1 hzK.2 _ hw'
      have h2 : (g⁻¹ * w * g) * z = z * (g⁻¹ * w * g) := by
        simpa using h1
      calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [h2]
        _ = (g * z * g⁻¹) * w := by group
    obtain ⟨v, hv, hcase⟩ := hKshape _ hgK
    have hcentE : ∀ e ∈ E, e * (g * z * g⁻¹) * e⁻¹ = g * z * g⁻¹ := by
      intro e he
      have he' : g⁻¹ * e * g ∈ E := by
        have := (Subgroup.mem_normalizer_iff.mp (h.normal (G.inv_mem hg)) e).mp he
        simpa using this
      have h3 : (g⁻¹ * e * g) * z * (g⁻¹ * e * g)⁻¹ = z := by
        rw [← hzE _ he']
        group
      calc e * (g * z * g⁻¹) * e⁻¹ = g * ((g⁻¹ * e * g) * z * (g⁻¹ * e * g)⁻¹) * g⁻¹ := by group
        _ = g * z * g⁻¹ := by rw [h3]
    have hzcentE : ∀ e ∈ E, e * z * e⁻¹ = z := by
      intro e he
      rw [← hzE e he]
      group
    rcases hcase with h1 | h1
    · exfalso
      have hv1 : g * z * g⁻¹ = 1 :=
        hV.centralizer_E_trivial h (v := g * z * g⁻¹) (h1 ▸ hv) hcentE
      apply hzV₁
      have h2 : z = 1 := by
        have := congrArg (fun x => g⁻¹ * x * g) hv1
        simpa [mul_assoc] using this
      rw [h2]
      exact V₁.one_mem
    · have hvc : ∀ e ∈ E, e * v * e⁻¹ = v := by
        intro e he
        have h2 := hcentE e he
        rw [h1] at h2
        have h3 := hzcentE e he
        calc e * v * e⁻¹ = (e * z * e⁻¹)⁻¹ * (e * (z * v) * e⁻¹) := by group
          _ = z⁻¹ * (z * v) := by rw [h3, h2]
          _ = v := by group
      have hv1 : v = 1 := hV.centralizer_E_trivial h hv hvc
      rw [hv1, mul_one] at h1
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [h1]
  · rw [hyz]
    simpa using V₁.inv_mem hv₁

end CFSG.CGT.PushingUpLit.SYMB
