module

public import CFSG.CGT.Hall82.Setting
public import CFSG.CGT.PushingUpLit.SolK.Local
public import CFSG.GroupTheory.SteinbergCBFTPSolvable

public section

namespace CFSG.CGT.Hall82

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open scoped commutatorElement IsMulCommutative

@[expose] def conjCocycle {G : Type*} [Group G] (x l : G) : G := x * l * x⁻¹ * l⁻¹

theorem conjCocycle_mul {G : Type*} [Group G] (x l₁ l₂ : G) :
    conjCocycle x (l₁ * l₂) = conjCocycle x l₁ * (l₁ * conjCocycle x l₂ * l₁⁻¹) := by
  simp only [conjCocycle]
  group

theorem conjCocycle_mul_mem_of_perfect {G : Type*} [Group G]
    {L V D : Subgroup G} {x : G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hDL : D ≤ Subgroup.centralizer (L : Set G))
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hDV : D ⊓ V = ⊥)
    (hDVc : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d)
    (hperf : ⁅L, L⁆ = L)
    (hδ : ∀ l ∈ L, ∃ d ∈ D, ∃ v ∈ V, conjCocycle x l = d * v) :
    ∀ l ∈ L, conjCocycle x l ∈ V := by
  classical
  have hdec : ∀ l ∈ L, ∃ d, d ∈ D ∧ ∃ v, v ∈ V ∧ conjCocycle x l = d * v :=
    fun l hl => hδ l hl
  let d : ↥L → G := fun l => Classical.choose (hdec l l.2)
  have hdD : ∀ l : ↥L, d l ∈ D := fun l => (Classical.choose_spec (hdec l l.2)).1
  let v : ↥L → G := fun l => Classical.choose (Classical.choose_spec (hdec l l.2)).2
  have hvV : ∀ l : ↥L, v l ∈ V :=
    fun l => (Classical.choose_spec (Classical.choose_spec (hdec l l.2)).2).1
  have hdvd : ∀ l : ↥L, conjCocycle x l = d l * v l :=
    fun l => (Classical.choose_spec (Classical.choose_spec (hdec l l.2)).2).2
  have hDVdisj : Disjoint D V := disjoint_iff.2 hDV
  have huniq : ∀ {d₁ d₂ v₁ v₂ : G}, d₁ ∈ D → d₂ ∈ D → v₁ ∈ V → v₂ ∈ V →
      d₁ * v₁ = d₂ * v₂ → d₁ = d₂ ∧ v₁ = v₂ := by
    intro d₁ d₂ v₁ v₂ hd₁ hd₂ hv₁ hv₂ h
    have hpair : ((⟨d₁, hd₁⟩, ⟨v₁, hv₁⟩) : ↥D × ↥V) =
        (⟨d₂, hd₂⟩, ⟨v₂, hv₂⟩) := by
      refine Subgroup.mul_injective_of_disjoint hDVdisj ?_
      simpa using h
    exact ⟨congrArg (fun p : ↥D × ↥V => (p.1 : G)) hpair,
      congrArg (fun p : ↥D × ↥V => (p.2 : G)) hpair⟩
  have hd_one : d 1 = 1 := by
    have h := (huniq (hdD 1) D.one_mem (hvV 1) V.one_mem (by
      rw [← hdvd 1]
      simp [conjCocycle])).1
    exact h
  have hd_mul : ∀ l₁ l₂ : ↥L, d (l₁ * l₂) = d l₁ * d l₂ := by
    intro l₁ l₂
    have hdl : (l₁ : G) * d l₂ * (l₁ : G)⁻¹ = d l₂ := by
      have hcomm := Subgroup.mem_centralizer_iff.1 (hDL (hdD l₂)) (l₁ : G) l₁.2
      calc (l₁ : G) * d l₂ * (l₁ : G)⁻¹ = (d l₂ * (l₁ : G)) * (l₁ : G)⁻¹ := by rw [hcomm]
        _ = d l₂ := by group
    have hwV : (l₁ : G) * v l₂ * (l₁ : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hLV l₁.2) (v l₂)).1 (hvV l₂)
    have hmid : (l₁ : G) * (d l₂ * v l₂) * (l₁ : G)⁻¹ =
        d l₂ * ((l₁ : G) * v l₂ * (l₁ : G)⁻¹) := by
      calc (l₁ : G) * (d l₂ * v l₂) * (l₁ : G)⁻¹
          = ((l₁ : G) * d l₂ * (l₁ : G)⁻¹) *
              ((l₁ : G) * v l₂ * (l₁ : G)⁻¹) := by group
        _ = d l₂ * ((l₁ : G) * v l₂ * (l₁ : G)⁻¹) := by rw [hdl]
    have hcalc : conjCocycle x ↑(l₁ * l₂) =
        (d l₁ * d l₂) * (v l₁ * ((l₁ : G) * v l₂ * (l₁ : G)⁻¹)) := by
      change conjCocycle x ((l₁ : G) * (l₂ : G)) =
        (d l₁ * d l₂) * (v l₁ * ((l₁ : G) * v l₂ * (l₁ : G)⁻¹))
      rw [conjCocycle_mul, hdvd l₁, hdvd l₂, hmid]
      calc (d l₁ * v l₁) * (d l₂ * ((l₁ : G) * v l₂ * (l₁ : G)⁻¹))
          = d l₁ * (v l₁ * d l₂) * ((l₁ : G) * v l₂ * (l₁ : G)⁻¹) := by group
        _ = d l₁ * (d l₂ * v l₁) * ((l₁ : G) * v l₂ * (l₁ : G)⁻¹) := by
            rw [← hDVc (d l₂) (hdD l₂) (v l₁) (hvV l₁)]
        _ = (d l₁ * d l₂) * (v l₁ * ((l₁ : G) * v l₂ * (l₁ : G)⁻¹)) := by group
    have hpair := huniq (hdD (l₁ * l₂)) (D.mul_mem (hdD l₁) (hdD l₂))
      (hvV (l₁ * l₂)) (V.mul_mem (hvV l₁) hwV) (by
        rw [← hdvd (l₁ * l₂), hcalc])
    exact hpair.1
  let φ : ↥L →* ↥D :=
    MonoidHom.mk' (fun l => ⟨d l, hdD l⟩) (fun l₁ l₂ => Subtype.ext (hd_mul l₁ l₂))
  haveI hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  haveI hcommD : IsMulCommutative ↥D :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hDc a.1 a.2 b.1 b.2))
  have hdtriv : ∀ l : ↥L, d l = 1 := fun l => by
    have hmemker : l ∈ φ.ker :=
      Abelianization.commutator_subset_ker φ
        (Group.IsPerfect.mem_commutator (G := ↥L) (g := l))
    have h : φ l = 1 := MonoidHom.mem_ker.1 hmemker
    simpa [φ] using congrArg Subtype.val h
  intro l hl
  change conjCocycle x (⟨l, hl⟩ : ↥L) ∈ V
  rw [hdvd ⟨l, hl⟩, hdtriv ⟨l, hl⟩, one_mul]
  exact hvV ⟨l, hl⟩

theorem exists_mul_mem_centralizer_of_cocycle {G : Type} [Group G] [Finite G]
    {L V D : Subgroup G} {z x : G}
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hDL : D ≤ Subgroup.centralizer (L : Set G))
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hDV : D ⊓ V = ⊥) (hDVc : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d)
    (hperf : ⁅L, L⁆ = L)
    (hzL : z ∈ L) (hzc : ∀ y ∈ L, y * z * y⁻¹ * z⁻¹ ∈ V)
    (hfpf : ∀ v ∈ V, z * v * z⁻¹ = v → v = 1)
    (hxV : ∀ v ∈ V, x * v * x⁻¹ = v)
    (hδ : ∀ l ∈ L, ∃ d ∈ D, ∃ v ∈ V, x * l * x⁻¹ * l⁻¹ = d * v) :
    ∃ v ∈ V, v * x ∈ Subgroup.centralizer (L : Set G) := by
  classical
  let δ : G → G := conjCocycle x
  have hδ' : ∀ l ∈ L, ∃ d ∈ D, ∃ v ∈ V, δ l = d * v := by
    intro l hl
    simpa [δ, conjCocycle] using hδ l hl
  have hδV : ∀ l ∈ L, δ l ∈ V :=
    conjCocycle_mul_mem_of_perfect hLV hDL hDc hDV hDVc hperf hδ'
  let w : ↥V → ↥V := fun v =>
    ⟨z * v.1 * z⁻¹, (Subgroup.mem_normalizer_iff.1 (hLV hzL) v.1).1 v.2⟩
  have hw_one : w 1 = 1 := by
    apply Subtype.ext
    simp [w]
  have hw_mul : ∀ a b : ↥V, w (a * b) = w a * w b := by
    intro a b
    apply Subtype.ext
    simp only [w, Subgroup.coe_mul]
    group
  let T : ↥V → ↥V := fun v => v⁻¹ * w v
  have hT_one : T 1 = 1 := by
    change (1 : ↥V)⁻¹ * w 1 = 1
    rw [hw_one, inv_one, one_mul]
  have hTmul : ∀ a b : ↥V, T (a * b) = T a * T b := by
    intro a b
    haveI : IsMulCommutative ↥V :=
      IsMulCommutative.of_comm (fun x y => Subtype.ext (hVc x.1 x.2 y.1 y.2))
    change (a * b)⁻¹ * w (a * b) = (a⁻¹ * w a) * (b⁻¹ * w b)
    rw [hw_mul, mul_inv_rev]
    ac_rfl
  have hT_inv : ∀ v : ↥V, T v⁻¹ = (T v)⁻¹ := by
    intro v
    have h := hTmul v v⁻¹
    rw [mul_inv_cancel, hT_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hTinj : Function.Injective T := by
    intro a b hab
    have h1 : T (a * b⁻¹) = 1 := by
      rw [hTmul, hT_inv, hab, mul_inv_cancel]
    have hc : (a * b⁻¹ : ↥V) = 1 := by
      apply Subtype.ext
      have hval : ((a * b⁻¹ : ↥V) : G)⁻¹ * (z * ((a * b⁻¹ : ↥V) : G) * z⁻¹) = 1 := by
        have := congrArg Subtype.val h1
        simpa [T, w] using this
      have hzc : z * ((a * b⁻¹ : ↥V) : G) * z⁻¹ = ((a * b⁻¹ : ↥V) : G) := by
        calc z * ((a * b⁻¹ : ↥V) : G) * z⁻¹
            = ((a * b⁻¹ : ↥V) : G) *
                (((a * b⁻¹ : ↥V) : G)⁻¹ * (z * ((a * b⁻¹ : ↥V) : G) * z⁻¹)) := by group
          _ = ((a * b⁻¹ : ↥V) : G) * 1 := by rw [hval]
          _ = ((a * b⁻¹ : ↥V) : G) := mul_one _
      exact hfpf _ (a * b⁻¹).2 hzc
    have : a = b := by
      have := congrArg (fun x : ↥V => x * b) hc
      simpa [mul_assoc] using this
    exact this
  haveI : Finite ↥V := inferInstance
  have hTsurj : Function.Surjective T := Finite.injective_iff_surjective.mp hTinj
  have hcoc : ∀ l ∈ L, δ z * (z * δ l * z⁻¹) = δ l * (l * δ z * l⁻¹) := by
    intro l hl
    let u : G := z * l * z⁻¹ * l⁻¹
    have huV : u ∈ V := by
      have h : (l * z * l⁻¹ * z⁻¹)⁻¹ ∈ V := V.inv_mem (hzc l hl)
      rwa [show (l * z * l⁻¹ * z⁻¹)⁻¹ = u by simp [u]; group] at h
    have hzl : z * l = u * (l * z) := by
      simp only [u]
      group
    have hδu : δ u = 1 := by
      have hx := hxV u huV
      change conjCocycle x u = 1
      simp only [conjCocycle, hx]
      group
    have h1 : δ (z * l) = δ z * (z * δ l * z⁻¹) := by
      change conjCocycle x (z * l) = conjCocycle x z * (z * conjCocycle x l * z⁻¹)
      exact conjCocycle_mul x z l
    have h2 : δ (z * l) = δ u * (u * δ (l * z) * u⁻¹) := by
      rw [hzl]
      change conjCocycle x (u * (l * z)) =
        conjCocycle x u * (u * conjCocycle x (l * z) * u⁻¹)
      exact conjCocycle_mul x u (l * z)
    have h3 : δ (l * z) = δ l * (l * δ z * l⁻¹) := by
      change conjCocycle x (l * z) = conjCocycle x l * (l * conjCocycle x z * l⁻¹)
      exact conjCocycle_mul x l z
    have huz : δ z * (z * δ l * z⁻¹) = u * (δ l * (l * δ z * l⁻¹)) * u⁻¹ := by
      calc δ z * (z * δ l * z⁻¹) = δ (z * l) := h1.symm
        _ = δ u * (u * δ (l * z) * u⁻¹) := h2
        _ = u * (δ l * (l * δ z * l⁻¹)) * u⁻¹ := by rw [hδu, h3]; group
    have hA : δ l ∈ V := hδV l hl
    have hZ : δ z ∈ V := hδV z hzL
    have hB : l * δ z * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hLV hl) (δ z)).1 hZ
    calc δ z * (z * δ l * z⁻¹) = u * (δ l * (l * δ z * l⁻¹)) * u⁻¹ := huz
      _ = δ l * (l * δ z * l⁻¹) := by
        have hcommA := hVc u huV (δ l) hA
        have hcommB := hVc u huV (l * δ z * l⁻¹) hB
        calc u * (δ l * (l * δ z * l⁻¹)) * u⁻¹
            = (u * δ l) * (l * δ z * l⁻¹) * u⁻¹ := by group
          _ = (δ l * u) * (l * δ z * l⁻¹) * u⁻¹ := by rw [hcommA]
          _ = δ l * (u * (l * δ z * l⁻¹)) * u⁻¹ := by group
          _ = δ l * ((l * δ z * l⁻¹) * u) * u⁻¹ := by rw [hcommB]
          _ = δ l * (l * δ z * l⁻¹) := by group
  have hTeq : ∀ (l : G) (hl : l ∈ L) (v : ↥V),
      (⟨l * (T v).1 * l⁻¹,
        (Subgroup.mem_normalizer_iff.1 (hLV hl) (T v).1).1 (T v).2⟩ : ↥V) =
      T ⟨l * v.1 * l⁻¹, (Subgroup.mem_normalizer_iff.1 (hLV hl) v.1).1 v.2⟩ := by
    intro l hl v
    apply Subtype.ext
    have hB : l * v.1 * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hl) v.1).1 v.2
    have hY : z * (l * v.1 * l⁻¹) * z⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hLV hzL) (l * v.1 * l⁻¹)).1 hB
    have hw₀V : l * z * l⁻¹ * z⁻¹ ∈ V := hzc l hl
    show l * (v.1⁻¹ * (z * v.1 * z⁻¹)) * l⁻¹ =
      (l * v.1 * l⁻¹)⁻¹ * (z * (l * v.1 * l⁻¹) * z⁻¹)
    let w₀ : G := l * z * l⁻¹ * z⁻¹
    let Y : G := z * (l * v.1 * l⁻¹) * z⁻¹
    have hwl : l * z * l⁻¹ = w₀ * z := by simp only [w₀]; group
    have hmain : l * (v.1⁻¹ * (z * v.1 * z⁻¹)) * l⁻¹ =
        (l * v.1 * l⁻¹)⁻¹ * w₀ * Y * w₀⁻¹ := by
      rw [show l * (v.1⁻¹ * (z * v.1 * z⁻¹)) * l⁻¹ =
          (l * v.1 * l⁻¹)⁻¹ * (l * z * l⁻¹) * (l * v.1 * l⁻¹) *
            (l * z * l⁻¹)⁻¹ from by group, hwl]
      simp only [Y, w₀]
      group
    rw [hmain]
    have hcomm := hVc w₀ hw₀V Y hY
    calc (l * v.1 * l⁻¹)⁻¹ * w₀ * Y * w₀⁻¹
        = (l * v.1 * l⁻¹)⁻¹ * (w₀ * Y) * w₀⁻¹ := by group
      _ = (l * v.1 * l⁻¹)⁻¹ * (Y * w₀) * w₀⁻¹ := by rw [hcomm]
      _ = (l * v.1 * l⁻¹)⁻¹ * Y := by group
      _ = (l * v.1 * l⁻¹)⁻¹ * (z * (l * v.1 * l⁻¹) * z⁻¹) := by rfl
  let Zv : ↥V := ⟨δ z, hδV z hzL⟩
  obtain ⟨v₀, hv₀⟩ := hTsurj Zv
  have hTδ : ∀ l : ↥L, T ⟨δ l, hδV l l.2⟩ =
      Zv⁻¹ * ⟨l.1 * δ z * l.1⁻¹, (Subgroup.mem_normalizer_iff.1 (hLV l.2) (δ z)).1
        (hδV z hzL)⟩ := by
    intro l
    apply Subtype.ext
    change (δ (l : G))⁻¹ * (z * δ (l : G) * z⁻¹) =
      (δ z)⁻¹ * ((l : G) * δ z * (l : G)⁻¹)
    have hid := hcoc l l.2
    have hA : δ (l : G) ∈ V := hδV l l.2
    have hZ : δ z ∈ V := hδV z hzL
    have hzA : z * δ (l : G) * z⁻¹ =
        (δ z)⁻¹ * (δ (l : G) * ((l : G) * δ z * (l : G)⁻¹)) := by
      calc z * δ (l : G) * z⁻¹ =
          (δ z)⁻¹ * (δ z * (z * δ (l : G) * z⁻¹)) := by group
        _ = (δ z)⁻¹ * (δ (l : G) * ((l : G) * δ z * (l : G)⁻¹)) := by rw [hid]
    calc (δ (l : G))⁻¹ * (z * δ (l : G) * z⁻¹)
        = (δ (l : G))⁻¹ *
            ((δ z)⁻¹ * (δ (l : G) * ((l : G) * δ z * (l : G)⁻¹))) := by rw [hzA]
      _ = ((δ (l : G))⁻¹ * (δ z)⁻¹) *
            (δ (l : G) * ((l : G) * δ z * (l : G)⁻¹)) := by group
      _ = ((δ z)⁻¹ * (δ (l : G))⁻¹) *
            (δ (l : G) * ((l : G) * δ z * (l : G)⁻¹)) := by
          rw [hVc (δ (l : G))⁻¹ (V.inv_mem hA) (δ z)⁻¹ (V.inv_mem hZ)]
      _ = (δ z)⁻¹ * ((l : G) * δ z * (l : G)⁻¹) := by group
  have hTv : ∀ l : ↥L, T ⟨v₀.1⁻¹ * (l.1 * v₀.1 * l.1⁻¹),
      V.mul_mem (V.inv_mem v₀.2) ((Subgroup.mem_normalizer_iff.1 (hLV l.2) v₀.1).1 v₀.2)⟩ =
      Zv⁻¹ * ⟨l.1 * δ z * l.1⁻¹, (Subgroup.mem_normalizer_iff.1 (hLV l.2) (δ z)).1
        (hδV z hzL)⟩ := by
    intro l
    have hB : l.1 * δ z * l.1⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hLV l.2) (δ z)).1 (hδV z hzL)
    have hlvV : l.1 * v₀.1 * l.1⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hLV l.2) v₀.1).1 v₀.2
    have hmem : v₀.1⁻¹ * (l.1 * v₀.1 * l.1⁻¹) ∈ V :=
      V.mul_mem (V.inv_mem v₀.2) hlvV
    calc T ⟨v₀.1⁻¹ * (l.1 * v₀.1 * l.1⁻¹), hmem⟩
        = T (v₀⁻¹ * ⟨l.1 * v₀.1 * l.1⁻¹, hlvV⟩) := by rfl
      _ = T (v₀⁻¹) * T ⟨l.1 * v₀.1 * l.1⁻¹, hlvV⟩ := hTmul _ _
      _ = (T v₀)⁻¹ * T ⟨l.1 * v₀.1 * l.1⁻¹, hlvV⟩ := by rw [hT_inv]
      _ = Zv⁻¹ * T ⟨l.1 * v₀.1 * l.1⁻¹, hlvV⟩ := by rw [hv₀]
      _ = Zv⁻¹ * (⟨l.1 * (T v₀).1 * l.1⁻¹,
            (Subgroup.mem_normalizer_iff.1 (hLV l.2) (T v₀).1).1 (T v₀).2⟩ : ↥V) := by
          rw [← hTeq l.1 l.2 v₀]
      _ = Zv⁻¹ * ⟨l.1 * δ z * l.1⁻¹, hB⟩ := by
          congr 1
          apply Subtype.ext
          change l.1 * (T v₀).1 * l.1⁻¹ = l.1 * δ z * l.1⁻¹
          rw [show (T v₀).1 = δ z from congrArg Subtype.val hv₀]
  have hδ_eq : ∀ l ∈ L, δ l = v₀.1⁻¹ * (l * v₀.1 * l⁻¹) := by
    intro l hl
    have h1 := hTδ ⟨l, hl⟩
    have h2 := hTv ⟨l, hl⟩
    exact congrArg Subtype.val (hTinj (h1.trans h2.symm))
  refine ⟨v₀.1, v₀.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hδl := hδ_eq l hl
  have hxl : x * l * x⁻¹ = δ l * l := by
    change x * l * x⁻¹ = conjCocycle x l * l
    simp only [conjCocycle]
    group
  have hconj : (v₀.1 * x) * l * (v₀.1 * x)⁻¹ = l := by
    calc (v₀.1 * x) * l * (v₀.1 * x)⁻¹
        = v₀.1 * (x * l * x⁻¹) * v₀.1⁻¹ := by group
      _ = v₀.1 * (δ l * l) * v₀.1⁻¹ := by rw [hxl]
      _ = v₀.1 * ((v₀.1⁻¹ * (l * v₀.1 * l⁻¹)) * l) * v₀.1⁻¹ := by rw [hδl]
      _ = l := by group
  calc l * (v₀.1 * x) = ((v₀.1 * x) * l * (v₀.1 * x)⁻¹) * (v₀.1 * x) := by rw [hconj]
    _ = (v₀.1 * x) * l := by group

theorem mem_sup_of_cocycle {G : Type} [Group G] [Finite G]
    {L V D : Subgroup G} {z x : G}
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hDL : D ≤ Subgroup.centralizer (L : Set G))
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hDV : D ⊓ V = ⊥) (hDVc : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d)
    (hperf : ⁅L, L⁆ = L)
    (hzL : z ∈ L) (hzc : ∀ y ∈ L, y * z * y⁻¹ * z⁻¹ ∈ V)
    (hfpf : ∀ v ∈ V, z * v * z⁻¹ = v → v = 1)
    (hxV : ∀ v ∈ V, x * v * x⁻¹ = v)
    (hδ : ∀ l ∈ L, ∃ d ∈ D, ∃ v ∈ V, x * l * x⁻¹ * l⁻¹ = d * v) :
    x ∈ V ⊔ Subgroup.centralizer (L : Set G) := by
  obtain ⟨v, hv, hvx⟩ := exists_mul_mem_centralizer_of_cocycle hVc hLV hDL hDc hDV hDVc hperf
    hzL hzc hfpf hxV hδ
  have hx : x = v⁻¹ * (v * x) := by group
  rw [hx]
  exact Subgroup.mul_mem_sup (V.inv_mem hv) hvx

theorem normalizer_blockU_eq_of_unique {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : IsShort L) (hN : Subgroup.normalizer (L : Set G) = M)
    (huniq : CFSG.maximalTwoLocalsContaining (L : Set G) = {M}) :
    Subgroup.normalizer (blockU L : Set G) = M := by
  have hMnormL : M ≤ Subgroup.normalizer (L : Set G) := by
    rw [hN]
  have hMnormQ : M ≤ Subgroup.normalizer (blockQ L : Set G) := by
    rw [← hN]
    simpa [blockQ] using CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L
  have hMnormU : M ≤ Subgroup.normalizer (blockU L : Set G) := by
    simpa [blockU] using CFSG.GroupTheory.FT63ChII.le_normalizer_commutator hMnormQ hMnormL
  have hLQ : L ≤ Subgroup.normalizer (blockQ L : Set G) := by
    simpa [blockQ] using CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) L
  have hLnormU : L ≤ Subgroup.normalizer (blockU L : Set G) := by
    simpa [blockU] using CFSG.GroupTheory.FT63ChII.le_normalizer_commutator hLQ
      Subgroup.le_normalizer
  have hUQ : blockU L ≤ blockQ L := hL.blockU_le_center.trans inf_le_left
  have hU2 : IsPGroup 2 (blockU L) :=
    CFSG.CGT.PushingUpLit.SolK.isPGroup_of_le (CFSG.CGT.PushingUpLit.SolK.isPGroup_pCoreOf' L) hUQ
  have hUne : blockU L ≠ ⊥ := by
    intro hbot
    have hZ : blockZ L = ⊥ := le_bot_iff.1 (hbot ▸ hL.blockZ_lt_blockU.le)
    have hlt := hL.blockZ_lt_blockU
    rw [hZ, hbot] at hlt
    exact (lt_irrefl (⊥ : Subgroup G)) hlt
  exact le_antisymm
    (CFSG.CGT.PushingUpLit.SolK.local_le_of_unique huniq ⟨blockU L, hUne, hU2, rfl⟩ hLnormU)
    hMnormU

namespace Setting

theorem normalizer_blockU_eq {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (S : Setting G M L) : Subgroup.normalizer (blockU L : Set G) = M :=
  normalizer_blockU_eq_of_unique S.short S.normalizer_eq S.uniq

theorem centralizer_blockU_le_M {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (S : Setting G M L) : Subgroup.centralizer (blockU L : Set G) ≤ M := by
  rw [← S.normalizer_blockU_eq]
  exact Subgroup.centralizer_le_normalizer _

theorem conj_mem_of_centralizer {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (S : Setting G M L) {x : G} (hx : x ∈ Subgroup.centralizer (blockU L : Set G))
    {l : G} (hl : l ∈ L) :
    x * l * x⁻¹ * l⁻¹ ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) := by
  have hxM : x ∈ M := S.centralizer_blockU_le_M hx
  have hlM : l ∈ M := S.le hl
  have hxlL : x * l * x⁻¹ ∈ L := S.normal hxM hl
  refine Subgroup.mem_inf.2 ⟨L.mul_mem hxlL (L.inv_mem hl), ?_⟩
  set C : Subgroup G := Subgroup.centralizer (blockU L : Set G) with hC
  have hCnorm : (C.subgroupOf (Subgroup.normalizer (blockU L : Set G))).Normal := by
    simpa [hC] using Subgroup.normal_subgroupOf_centralizer_normalizer (blockU L : Set G)
  have hle : Subgroup.normalizer (blockU L : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).1 hCnorm
  have hlN : l ∈ Subgroup.normalizer (C : Set G) := by
    refine hle ?_
    rw [S.normalizer_blockU_eq]
    exact hlM
  have hconj : l * x * l⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 hlN x).1 hx
  have heq : x * l * x⁻¹ * l⁻¹ = x * (l * x * l⁻¹)⁻¹ := by group
  rw [heq]
  exact C.mul_mem hx (C.inv_mem hconj)

end Setting

end CFSG.CGT.Hall82
