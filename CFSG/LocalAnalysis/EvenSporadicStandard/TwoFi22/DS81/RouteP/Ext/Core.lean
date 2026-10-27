module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.CertSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Order
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.OrderM24

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen Certificates.RouteP.M24Defect

universe u v

theorem wordProd_congr {G : Type*} [Group G] {x y : ℕ → G} {w : List (ℕ × Bool)}
    (h : ∀ l ∈ w, x l.1 = y l.1) : wordProd x w = wordProd y w := by
  unfold wordProd
  congr 1
  refine List.map_congr_left fun l hl => ?_
  simp only [h l hl]

theorem π_img2 {G H : Type*} [Group G] [Group H] (π : G →* H) {x y : G} {a b : H}
    (hx : π x = a) (hy : π y = b) (i : ℕ) : π (img2 x y i) = img2 a b i := by
  unfold img2
  split_ifs
  · exact hx
  · exact hy

theorem img2_mul_of_lt {G : Type*} [Group G] (z : ℕ → G) (x y : G) {i : ℕ} (hi : i < 2) :
    img2 (z 0 * x) (z 1 * y) i = z i * img2 x y i := by
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl <;> simp [img2]

section Construction

variable {N : Type u} {N₀ : Type v} [Group N] [Group N₀]

open scoped Classical in
@[expose] noncomputable def extendOn (B : Subgroup N) (B₀ : Subgroup N₀) (φ : ↥B ≃* ↥B₀)
    (n : N) : N₀ :=
  if hn : n ∈ B then ((φ ⟨n, hn⟩ : ↥B₀) : N₀) else 1

open scoped Classical in
theorem extendOn_of_mem {B : Subgroup N} {B₀ : Subgroup N₀} (φ : ↥B ≃* ↥B₀) {n : N}
    (hn : n ∈ B) : extendOn B B₀ φ n = ((φ ⟨n, hn⟩ : ↥B₀) : N₀) :=
  dif_pos hn

open scoped Classical in
@[expose] noncomputable def sectionOn {M : Type*} [Group M] (π : N →* M)
    (hπ : Function.Surjective π) (k : M) : N :=
  if k = 1 then 1 else Classical.choose (hπ k)

open scoped Classical in
theorem sectionOn_one {M : Type*} [Group M] (π : N →* M) (hπ : Function.Surjective π) :
    sectionOn π hπ 1 = 1 := if_pos rfl

open scoped Classical in
theorem π_sectionOn {M : Type*} [Group M] (π : N →* M) (hπ : Function.Surjective π) (k : M) :
    π (sectionOn π hπ k) = k := by
  unfold sectionOn
  split_ifs with h
  · rw [map_one, h]
  · exact Classical.choose_spec (hπ k)

variable {X : ExtData (rho11 AutPerm le_rfl) N} {X₀ : ExtData (rho11 AutPerm le_rfl) N₀}

noncomputable def mkDefectData (hC : treeOK (treeTab ()) = true)
    (hL : treeLetters (treeTab ()) = true) {B : Subgroup N} {B₀ : Subgroup N₀}
    (hB : ∀ n, n ∈ B ↔ X.π n ∈ K22) (φ : ↥B ≃* ↥B₀)
    (hφπ : ∀ b : ↥B, X₀.π (φ b) = X.π b)
    (hφe : ∀ b : ↥B, X.π b = 1 → X₀.eT (φ b) = X.eT b)
    {xt : ℕ → N} (hxt : ∀ i, X.π (xt i) = gens i) {xt₀ : ℕ → N₀}
    (hxt₀ : ∀ i, X₀.π (xt₀ i) = gens i) : DefectData X X₀ K22 gens where
  θ := extendOn B B₀ φ
  θ_mul b b' hb hb' := by
    have h1 : b ∈ B := (hB b).2 hb
    have h2 : b' ∈ B := (hB b').2 hb'
    rw [extendOn_of_mem φ (B.mul_mem h1 h2), extendOn_of_mem φ h1, extendOn_of_mem φ h2]
    exact congrArg Subtype.val (map_mul φ ⟨b, h1⟩ ⟨b', h2⟩)
  θ_π b hb := by
    have h1 : b ∈ B := (hB b).2 hb
    rw [extendOn_of_mem φ h1]
    exact hφπ ⟨b, h1⟩
  θ_eT x hx := by
    have h1 : x ∈ B := (hB x).2 (by rw [hx]; exact K22.one_mem)
    rw [extendOn_of_mem φ h1]
    exact hφe ⟨x, h1⟩ hx
  β := sectionOn X.π X.π_surjective
  β_π k _ := π_sectionOn X.π X.π_surjective k
  β_one := sectionOn_one X.π X.π_surjective
  q := qFun
  tr := trFun
  q_mul k hk h := qFun_mul hk h
  tr_mem h := kOf_trFun_mem hC hL h
  σ c := sectionOn X.π X.π_surjective (trFun c)
  σ_π c := π_sectionOn X.π X.π_surjective (trFun c)
  σ₀ c := sectionOn X₀.π X₀.π_surjective (trFun c)
  σ₀_π c := π_sectionOn X₀.π X₀.π_surjective (trFun c)
  xt := xt
  xt_π := hxt
  xt₀ := xt₀
  xt₀_π := hxt₀

end Construction

section Main

variable {N : Type u} {N₀ : Type v} [Group N] [Group N₀]
  {X : ExtData (rho11 AutPerm le_rfl) N} {X₀ : ExtData (rho11 AutPerm le_rfl) N₀}

theorem exists_mulEquiv_of_extData
    {B : Subgroup N} {B₀ : Subgroup N₀}
    (hB : ∀ n, n ∈ B ↔ X.π n ∈ K22) (θ : ↥B ≃* ↥B₀)
    (hθπ : ∀ b : ↥B, X₀.π (θ b) = X.π b)
    (hθe : ∀ b : ↥B, X.π b = 1 → X₀.eT (θ b) = X.eT b) :
    ∃ Ψ : N ≃* N₀, (∀ x, X.π x = 1 → X₀.eT (Ψ x) = X.eT x) ∧ ∀ n, X₀.π (Ψ n) = X.π n := by
  have hcheck : checkAll () = true := Certificates.certificate450210
  obtain ⟨hrels, hC, hL, -⟩ := checkAll_spec hcheck
  obtain ⟨xa, hxa⟩ := X.π_surjective genA
  obtain ⟨xb, hxb⟩ := X.π_surjective genB
  obtain ⟨xa₀, hxa₀⟩ := X₀.π_surjective genA
  obtain ⟨xb₀, hxb₀⟩ := X₀.π_surjective genB
  have hxt : ∀ i, X.π (img2 xa xb i) = gens i := π_img2 X.π hxa hxb
  have hxt₀ : ∀ i, X₀.π (img2 xa₀ xb₀ i) = gens i := π_img2 X₀.π hxa₀ hxb₀
  let D := mkDefectData hC hL hB θ hθπ hθe hxt hxt₀
  obtain ⟨z, hzπ, hz⟩ := exists_changeLifts D rfl rfl
  have hxa' : X.π (z 0 * xa) = genA := by rw [map_mul, hzπ, one_mul, hxa]
  have hxb' : X.π (z 1 * xb) = genB := by rw [map_mul, hzπ, one_mul, hxb]
  have hmatch : ∀ r ∈ relWords, X.eT (wordProd (img2 (z 0 * xa) (z 1 * xb)) r) =
      X₀.eT (wordProd (img2 xa₀ xb₀) r) := fun r hr => by
    have h2 : wordProd (img2 (z 0 * xa) (z 1 * xb)) r = wordProd (fun i => z i * D.xt i) r :=
      wordProd_congr fun l hl => img2_mul_of_lt z xa xb (relWords_letters r hr l hl)
    exact (congrArg X.eT h2).trans (hz r hr)
  exact exists_mulEquiv_of_matching_defects X X₀ closure_genA_genB hxa' hxb' hxa₀ hxb₀
    (R := relWords) (wordProd_relWords hrels) hmatch
    (fun G _ x y hxy => exists_subgroup_card_le_autPerm x y hxy)

end Main

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
