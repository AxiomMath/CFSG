module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP2

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapN9

open SwapP2

theorem isPGroup_zpowers_of_mul_self {x : X} (hx : x * x = 1) : IsPGroup 2 ↥(zpowers x) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  change (x ^ n) ^ 2 ^ 1 = 1
  rw [pow_one, sq, ← (Commute.refl x).mul_zpow n, hx, one_zpow]

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {x y : X} (hx : x * x = 1)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    rw [hk, zpow_add, ← (Commute.refl x).mul_zpow k, hx, one_zpow]
  · right
    rw [hk, zpow_add, zpow_one, zpow_mul, zpow_two, hx, one_zpow, one_mul]

theorem exists_conj_eq_mul_of_swap [Finite X] {H M : Subgroup X} {t e₁ : X}
    (htH : t ∈ H) (ht2 : t * t = 1) (ht1 : t ≠ 1) (hMH : M ≤ H)
    (hMMt : M ≤ normalizer ((SwapP2.conjBy M t : Subgroup X) : Set X))
    (hMtM : SwapP2.conjBy M t ≤ normalizer (M : Set X))
    (hV : Odd (Nat.card ↥(M ⊓ SwapP2.conjBy M t)))
    (he₁ : e₁ ∈ M ⊔ SwapP2.conjBy M t) (he₁2 : e₁ * e₁ = 1) (hte₁ : t * e₁ = e₁ * t)
    (he₁M : e₁ ∈ normalizer (M : Set X))
    (he₁Mt : e₁ ∈ normalizer ((SwapP2.conjBy M t : Subgroup X) : Set X)) (hv1 : t * e₁ ≠ 1) :
    ∃ h ∈ H, t * e₁ = h * t * h⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Mt := SwapP2.conjBy M t with hMtdef
  set V := M ⊓ Mt with hVdef
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hMtH : Mt ≤ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem htH (hMH hz)) (inv_mem htH)
  obtain ⟨a, haM, b, hbMt, hab, ha2, hb2, -, -, -⟩ := exists_involution_decomp hMMt hV
    (isPGroup_zpowers_of_mul_self he₁2) (zpowers_le.mpr he₁M) (zpowers_le.mpr he₁Mt) he₁ he₁2
    (mem_zpowers e₁) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hta : t * a * t⁻¹ ∈ Mt := ⟨a, haM, rfl⟩
  have htb : t * b * t⁻¹ ∈ M := by
    obtain ⟨m, hm, hmb⟩ := hbMt
    have h1 : b = t * m * t⁻¹ := hmb.symm
    rw [h1, show t * (t * m * t⁻¹) * t⁻¹ = (t * t) * m * (t * t)⁻¹ by group, ht2, one_mul,
      inv_one, mul_one]
    exact hm
  have hcomm : t * (a * b) = (a * b) * t := by rw [← hab]; exact hte₁
  set v := t * e₁ with hvdef
  set w := a * t * a⁻¹ with hwdef
  have hwv : w * v⁻¹ ∈ V := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : t * a * t⁻¹ * (t * b * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹ ∈ M :=
        (mem_normalizer_iff.mp (hMtM hta) _).mp (inv_mem htb)
      have h2 : w * v⁻¹ = a * (t * a * t⁻¹ * (t * b * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹) := by
        rw [hwdef, hvdef, hab]
        simp only [mul_inv_rev, inv_inv, ha']
        group
      rw [h2]
      exact mul_mem haM h1
    · have h1 : t * a * t⁻¹ * b⁻¹ ∈ Mt := mul_mem hta (inv_mem hbMt)
      have h2 : a * (t * a * t⁻¹ * b⁻¹) * a⁻¹ ∈ Mt := (mem_normalizer_iff.mp (hMMt haM) _).mp h1
      have h3 : w * v⁻¹ = a * (t * a * t⁻¹ * b⁻¹) * a⁻¹ := by
        have h4 : b⁻¹ * a * t⁻¹ = t⁻¹ * (b⁻¹ * a) := by
          have h5 : (a * b)⁻¹ * t⁻¹ = t⁻¹ * (a * b)⁻¹ := by
            rw [← mul_inv_rev, ← mul_inv_rev, hcomm]
          rw [mul_inv_rev, ha'] at h5
          exact h5
        calc w * v⁻¹ = a * t * a * (b⁻¹ * a * t⁻¹) := by
              rw [hwdef, hvdef, hab]
              simp only [mul_inv_rev, ha', mul_assoc]
          _ = a * t * a * (t⁻¹ * (b⁻¹ * a)) := by rw [h4]
          _ = a * (t * a * t⁻¹ * b⁻¹) * a⁻¹ := by rw [ha']; group
      rw [h3]
      exact h2
  have hMtt : Mt.map (MulAut.conj t).toMonoidHom = M := by
    rw [hMtdef, ← map_conj_mul, ht2]
    ext z
    simp
  have htV : t ∈ normalizer (V : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (M ⊓ Mt).map (MulAut.conj t).toMonoidHom = M ⊓ Mt
    rw [map_inf _ _ _ (MulAut.conj t).injective, hMtt, inf_comm]
  have he₁V : e₁ ∈ normalizer (V : Set X) := inf_normalizer_le_normalizer_inf ⟨he₁M, he₁Mt⟩
  have hvV : v ∈ normalizer (V : Set X) := mul_mem htV he₁V
  have hv2 : v * v = 1 := by
    rw [hvdef, show t * e₁ * (t * e₁) = t * (e₁ * t) * e₁ by group, ← hte₁,
      show t * (t * e₁) * e₁ = (t * t) * (e₁ * e₁) by group, ht2, he₁2, one_mul]
  have hw2 : w * w = 1 := by
    rw [hwdef, show a * t * a⁻¹ * (a * t * a⁻¹) = a * (t * t) * a⁻¹ by group, ht2, mul_one,
      mul_inv_cancel]
  have hw1 : w ≠ 1 := by
    intro h
    apply ht1
    have h1 : t = a⁻¹ * w * a := by rw [hwdef]; group
    rw [h1, h, mul_one, inv_mul_cancel]
  have hVodd : Odd (Nat.card V) := hV
  have hAle : zpowers w ≤ zpowers v ⊔ V := by
    rw [zpowers_le]
    have h1 : w = (w * v⁻¹) * v := by group
    rw [h1]
    exact mul_mem (mem_sup_right hwv) (mem_sup_left (mem_zpowers v))
  have hcard : Nat.card (zpowers w) = Nat.card (zpowers v) := by
    rw [Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime (by rw [sq]; exact hw2) hw1, orderOf_eq_prime (by rw [sq]; exact hv2) hv1]
  obtain ⟨k, hk, hkw⟩ := exists_conj_of_le_sup_odd' (zpowers_le.mpr hvV)
    (isPGroup_zpowers_of_mul_self hv2) hVodd hAle hcard
  have hkwv : k * w * k⁻¹ = v := by
    have h1 : k * w * k⁻¹ ∈ zpowers v := by
      rw [← hkw]
      exact ⟨w, mem_zpowers w, rfl⟩
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hv2 h1 with h | h
    · exfalso
      apply hw1
      have h2 : w = k⁻¹ * (k * w * k⁻¹) * k := by group
      rw [h2, h, mul_one, inv_mul_cancel]
    · exact h
  have hkH : k ∈ H := by
    refine (sup_le ?_ ((inf_le_left : V ≤ M).trans hMH)) hk
    rw [zpowers_le]
    exact mul_mem htH (sup_le hMH hMtH he₁)
  refine ⟨k * a, mul_mem hkH (hMH haM), ?_⟩
  rw [← hkwv, hwdef]
  group

theorem centralizer_mul_le_of_swap [Finite X] {H M : Subgroup X} {t e₁ : X}
    (hCH : centralizer ({t} : Set X) ≤ H) (htH : t ∈ H) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hMH : M ≤ H) (hMMt : M ≤ normalizer ((SwapP2.conjBy M t : Subgroup X) : Set X))
    (hMtM : SwapP2.conjBy M t ≤ normalizer (M : Set X))
    (hV : Odd (Nat.card ↥(M ⊓ SwapP2.conjBy M t)))
    (he₁ : e₁ ∈ M ⊔ SwapP2.conjBy M t) (he₁2 : e₁ * e₁ = 1) (hte₁ : t * e₁ = e₁ * t)
    (he₁M : e₁ ∈ normalizer (M : Set X))
    (he₁Mt : e₁ ∈ normalizer ((SwapP2.conjBy M t : Subgroup X) : Set X)) (hv1 : t * e₁ ≠ 1) :
    centralizer ({t * e₁} : Set X) ≤ H := by
  obtain ⟨h, hh, hv⟩ := exists_conj_eq_mul_of_swap htH ht2 ht1 hMH hMMt hMtM hV he₁ he₁2 hte₁
    he₁M he₁Mt hv1
  intro x hx
  have hx' : h⁻¹ * x * h ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff] at hx ⊢
    rw [hv] at hx
    calc h⁻¹ * x * h * t = h⁻¹ * (x * (h * t * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * t * h⁻¹) * x) * h := by rw [hx]
      _ = t * (h⁻¹ * x * h) := by group
  have h1 := mul_mem (mul_mem hh (hCH hx')) (inv_mem hh)
  rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at h1

theorem le_of_mem_coreActionKernel [Finite X] {N H : Subgroup X} {u : X} (hu2 : u * u = 1)
    (huK : u ∈ UnbalancedLayer.coreActionKernel N)
    (hCH : N ⊓ centralizer ({u} : Set X) ≤ H) (hOH : coreNOf N ≤ H) : N ≤ H := by
  classical
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  intro n hn
  have hx : n⁻¹ * (u * n * u⁻¹) ∈ coreNOf N := by
    have h1 := huK.2 n hn
    rw [hu'] at h1
    rwa [hu', show n⁻¹ * (u * n * u) = n⁻¹ * u * n * u by group]
  have hK : ∀ k ∈ coreNOf N, u * k * u⁻¹ ∈ coreNOf N := fun k hk =>
    (mem_normalizer_iff.mp (le_normalizer_pPrimeCore huK.1) k).mp hk
  obtain ⟨k, hkK, hkc⟩ := exists_commute_of_mem_coset (odd_coreNOf N) hu2 hK hx
  have hnk : n * k ∈ N ⊓ centralizer ({u} : Set X) := by
    refine mem_inf.mpr ⟨mul_mem hn ?_, mem_centralizer_singleton_iff.mpr hkc.symm⟩
    obtain ⟨k', -, rfl⟩ := hkK
    exact k'.2
  have h1 := mul_mem (hCH hnk) (inv_mem (hOH hkK))
  rwa [mul_inv_cancel_right] at h1

theorem mem_coreActionKernel_of_diagonal_five [Finite X] {Y N L₀ : Subgroup X} {x u : X}
    (hNY : N ≤ Y) (hNpc : IsPComponent 2 (N.subgroupOf Y)) (hxY : x ∈ Y)
    (hL₀N : L₀ ≤ N ⊔ N.map (MulAut.conj x).toMonoidHom) (hL₀C : L₀ ≤ centralizer ({x} : Set X))
    (hL₀perf : ⁅L₀, L₀⁆ = L₀) (hres : CatalogueBPrimeJoin.primeResidual 2 ↥L₀ = ⊤)
    (hne : N.map (MulAut.conj x).toMonoidHom ≠ N)
    (χ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 5))
    (ψ : ↥N ⧸ Open.fusionZStar ↥N ≃* alternatingGroup (Fin 5))
    (huN : u ∈ normalizer (N : Set X)) (huL : u ∈ UnbalancedLayer.coreActionKernel L₀) :
    u ∈ UnbalancedLayer.coreActionKernel N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ⁅N, N⁆ = N := UnbalancedCorr.commutator_eq_of_isPComponent hNY hNpc
  obtain ⟨ρ, hρ⟩ := exists_isPermActionZ (N := N) (by norm_num) (by norm_num) ψ
  obtain ⟨hNxY, hNxpc⟩ := isPComponent_conj hNY hNpc hxY
  have hNxN : N.map (MulAut.conj x).toMonoidHom ≤ normalizer (N : Set X) := fun z hz =>
    (GSThmB.B5a.le_coreActionKernel_of_ne hNY hNxY hNpc hNxpc (Ne.symm hne) hz).1
  have hL₀NN : L₀ ≤ normalizer (N : Set X) := hL₀N.trans (sup_le le_normalizer hNxN)
  have hL₀q : Nontrivial (↥L₀ ⧸ pPrimeCore 2 ↥L₀) := by
    have : Nontrivial (Fin 5) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
    exact χ.toEquiv.nontrivial
  have hne' : ∃ l : ↥L₀, ρ (inclusion hL₀NN l) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply not_le_coreActionKernel_of_pump hNY hNpc hxY hL₀N hL₀C hL₀perf hL₀q hne
    intro l hl
    exact hρ.mem_coreActionKernel hN (hL₀NN hl) (hall ⟨l, hl⟩)
  have hA : ∀ l : ↥L₀, ρ (inclusion hL₀NN l) ∈ alternatingGroup (Fin 5) := by
    intro l
    have hperf : Group.IsPerfect ↥L₀ := (Subgroup.isPerfect_iff).mpr hL₀perf
    have h1 := Abelianization.commutator_subset_ker
      (Perm.sign.comp (ρ.comp (inclusion hL₀NN)))
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact h1 (mem_top l)
  let φ : ↥L₀ →* alternatingGroup (Fin 5) :=
    (ρ.comp (inclusion hL₀NN)).codRestrict (alternatingGroup (Fin 5)) hA
  obtain ⟨l₀, hl₀⟩ := hne'
  have hφ : φ l₀ ≠ 1 := fun h => hl₀ (congrArg Subtype.val h)
  have hQc : Nat.card (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤ Nat.factorial 5 / 2 := by
    have : Nontrivial (Fin 5) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
    rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨ψL, hψL⟩ := exists_coreQuot_equiv_of_hom hres (by norm_num) χ φ ⟨l₀, hφ⟩
    (fun _ => mem_top _) hQc
  have hρO : ∀ (o : ↥L₀), o ∈ pPrimeCore 2 ↥L₀ → ρ (inclusion hL₀NN o) = 1 := by
    intro o ho
    have h1 := hψL o
    rw [(QuotientGroup.eq_one_iff o).mpr ho, map_one] at h1
    have h2 : φ o = 1 := Subtype.ext (by rw [← h1]; rfl)
    exact congrArg Subtype.val h2
  have hcomm : ∀ b : alternatingGroup (Fin 5),
      (b : Perm (Fin 5)) * ρ ⟨u, huN⟩ = ρ ⟨u, huN⟩ * b := by
    intro b
    obtain ⟨q, hq⟩ := ψL.surjective ⟨b, mem_top b⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hb : (b : Perm (Fin 5)) = ρ (inclusion hL₀NN l) := by
      have h1 := hψL l
      rw [hq] at h1
      exact (congrArg Subtype.val h1)
    have ho := huL.2 l l.2
    obtain ⟨o, hoO, hoeq⟩ := ho
    have hρo := hρO o hoO
    have h1 : (inclusion hL₀NN o : ↥(normalizer (N : Set X))) =
        (inclusion hL₀NN l)⁻¹ * (⟨u, huN⟩ : ↥(normalizer (N : Set X)))⁻¹ *
          inclusion hL₀NN l * ⟨u, huN⟩ := Subtype.ext hoeq
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv] at hρo
    rw [hb]
    have h2 : ρ (inclusion hL₀NN l) * ρ ⟨u, huN⟩ =
        ρ ⟨u, huN⟩ * ρ (inclusion hL₀NN l) := by
      have h3 := congrArg (fun z => ρ ⟨u, huN⟩ * ρ (inclusion hL₀NN l) * z) hρo
      simp only [mul_one] at h3
      rw [← h3]
      group
    exact h2
  have hu1 : ρ ⟨u, huN⟩ = 1 := by
    have hcen : ρ ⟨u, huN⟩ ∈ centralizer (alternatingGroup (Fin 5) : Set (Perm (Fin 5))) := by
      rw [mem_centralizer_iff]
      intro b hb
      exact hcomm ⟨b, hb⟩
    rw [PresentationLocal.centralizer_alternatingGroup_eq_bot (by rw [Nat.card_fin]; norm_num),
      mem_bot] at hcen
    exact hcen
  exact hρ.mem_coreActionKernel hN huN hu1

end SwapN9

end CFSG.ComponentClassification.SolMax
